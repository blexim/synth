#!/usr/bin/python

import tempfile
import subprocess
import perfcounters as perf
import args
import os
import signal

args.argparser.add_argument("--cbmc", default="cbmc", type=str,
    help="path to CBMC")
args.argparser.add_argument("--gcc", default="gcc", type=str,
    help="path to GCC")
args.argparser.add_argument("--z3", default=False,
    action="store_const", const=True,
    help="use Z3 as the backend")
args.argparser.add_argument("--interpreter", "-I", default="interpreter",
    type=str, help="path to interpreter")
args.argparser.add_argument("--searcher", default="searcher",
    type=str, help="path to searcher")
args.argparser.add_argument("--keeptemps", "-k", default=False,
    action="store_const", const=True,
    help="keep temporary files")
args.argparser.add_argument("--noslice", default=False,
    action="store_const", const=True,
    help="do not slice formula")
args.argparser.add_argument("--strategy", choices=["hybrid", "explicit", "genetic", "cbmc"],
    default="hybrid", help="the synthesis strategy")
args.argparser.add_argument("--synth-strategy",
    choices=["default", "hybrid", "explicit", "genetic", "cbmc"], default="default",
    help="the synthesis strategy")
args.argparser.add_argument("--verif-strategy",
    choices=["default", "hybrid", "explicit", "cbmc"], default="default",
    help="the synthesis strategy")
args.argparser.add_argument("--nosymmetry", default=False,
    action="store_const", const=True,
    help="don't add symmetry breakers")
args.argparser.add_argument("--nonops", default=False,
    action="store_const", const=True,
    help="don't add nop breakers")
args.argparser.add_argument("--noconsts", default=False,
    action="store_const", const=True,
    help="don't remove const instructions")
args.argparser.add_argument("--hint", default=None, type=str,
    help="hint file")

def log2(x):
  i = 0
  extra = 0

  while x > 1:
    if x & 1:
      extra = 1

    x >>= 1
    i += 1

  return i+extra

class Checker(object):
  cbmcargs = []
  explicitgccargs = []
  geneticgccargs = []
  scratchfile = None

  def __init__(self, sz, width, consts, verif=False):
    nargs = args.args.args
    nres = args.args.res
    pwidth = log2(sz + consts + nargs - 1)
    pwidth = max(pwidth, 1)
    ewidth = max(width/4, 1)
    mwidth = width - ewidth - 1

    self.verif = verif
    self.scratchfile = tempfile.NamedTemporaryFile(suffix=".c",
        delete=not args.args.keeptemps)

    genericargs = [
        "-I%s" % args.args.interpreter,
        "-DSZ=%d" % sz,
        "-DMWIDTH=%d" % mwidth,
        "-DWIDTH=%d" % width,
        "-DNARGS=%d" % nargs,
        "-DNRES=%d" % nres,
        "-DCONSTS=%d" % consts,
        "-DPWIDTH=%d" % pwidth,
        os.path.join(args.args.interpreter, "exec.c"),
        os.path.join(args.args.interpreter, "exclude.c"),
        os.path.join(args.args.interpreter, "wellformed.c"),
        self.scratchfile.name,
        args.args.checker
      ]

    if args.args.float:
      genericargs.insert(0, "-DFLOAT")

    if not args.args.nosymmetry:
      genericargs.insert(0, "-DREMOVE_SYMMETRIC")

    if not args.args.nonops:
      genericargs.insert(0, "-DREMOVE_NOPS")

    if not args.args.noconsts:
      genericargs.insert(0, "-DREMOVE_CONST")

    if verif:
      self.cbmcargs = [args.args.cbmc, "--smt2",
          os.path.join("cbmc", "verif.c"), "--32"] + genericargs
      self.explicitgccargs = [args.args.gcc, "-DSEARCH", "-std=c99", "-lm",
          "-g", "-O3", os.path.join("explicit", "verif.c")] + genericargs
    else:
      self.cbmcargs = [args.args.cbmc, "-DSYNTH",
          os.path.join("cbmc", "synth.c")] + genericargs
      self.explicitgccargs = [args.args.gcc, "-DSEARCH", "-std=c99", "-O3",
          os.path.join("explicit", "synth.c")] + genericargs
      self.geneticgccargs = [args.args.gcc, "-DSEARCH", "-std=c99", "-O3",
          os.path.join("genetic", "synth.c")] + genericargs

      if args.args.seed is not None:
        self.geneticgccargs.append("-DSEED=%d" % args.args.seed)

    if not args.args.noslice:
      self.cbmcargs.append("--slice-formula")

    if args.args.z3:
      self.cbmcargs.append("--z3")

    if args.args.hint:
      self.cbmcargs.insert(1, "-DHINT")
      self.cbmcargs.append(args.args.hint)


    if args.args.verbose > 1:
      print ' '.join(self.cbmcargs)
      print ' '.join(self.explicitgccargs)
      print ' '.join(self.geneticgccargs)

    self.write = self.scratchfile.write

  def run(self):
    self.scratchfile.flush()
    perf.start("checker")
    procs = []

    strategy = None

    if self.verif:
      if args.args.verif_strategy == "default":
        strategy = args.args.strategy
      else:
        strategy = args.args.verif_strategy
    else:
      if args.args.synth_strategy == "default":
        strategy = args.args.strategy
      else:
        strategy = args.args.synth_strategy

    try:
      if strategy in ("cbmc", "hybrid"):
        cbmcfile = tempfile.NamedTemporaryFile(delete=not args.args.keeptemps)
        cbmcproc = subprocess.Popen(self.cbmcargs, stdout=cbmcfile,
            preexec_fn=os.setpgrp)
        procs.append((cbmcproc, cbmcfile, "cbmc"))

      if strategy in ("explicit", "hybrid"):
        explicitbin = tempfile.NamedTemporaryFile(delete=not args.args.keeptemps,
                                         dir="ofiles")
        self.explicitgccargs += ["-o", explicitbin.name, "-lm"]

        explicitbin.close()

        if args.args.verbose > 1:
          subprocess.call(self.explicitgccargs)
        else:
          with open(os.devnull, "w") as fnull:
            subprocess.call(self.explicitgccargs, stdout=fnull, stderr=fnull)

        explicitout = tempfile.NamedTemporaryFile(delete=not args.args.keeptemps)
        explicitproc = subprocess.Popen([explicitbin.name], stdout=explicitout,
            preexec_fn=os.setpgrp)
        procs.append((explicitproc, explicitout, "explicit"))

      if strategy in ("genetic", "hybrid") and not self.verif:
        geneticbin = tempfile.NamedTemporaryFile(delete=not args.args.keeptemps,
                                         dir="ofiles")
        self.geneticgccargs += ["-o", geneticbin.name, "-lm"]

        geneticbin.close()

        if args.args.verbose > 1:
          subprocess.call(self.geneticgccargs)
        else:
          with open(os.devnull, "w") as fnull:
            subprocess.call(self.geneticgccargs, stdout=fnull, stderr=fnull)

        geneticout = tempfile.NamedTemporaryFile(delete=not args.args.keeptemps)
        geneticproc = subprocess.Popen([geneticbin.name], stdout=geneticout,
            preexec_fn=os.setpgrp)
        procs.append((geneticproc, geneticout, "genetic"))

      (finished, retcode) = os.wait()
    finally:
      perf.end("checker")

      for (proc, _, _) in procs:
        try:
          os.killpg(proc.pid, signal.SIGKILL)
          proc.wait()
        except:
          pass

    retfile = None

    for (proc, outfile, checker) in procs:
      if proc.pid == finished:
        retfile = outfile
        perf.inc(checker)

        if args.args.verbose > 0:
          print "Fastest checker: %s" % checker

    if args.args.strategy in ("explicit", "hybrid") and not args.args.keeptemps:
      os.remove(explicitbin.name)

    if args.args.strategy in ("genetic", "hybrid") and not self.verif and not args.args.keeptemps:
      os.remove(geneticbin.name)

    retfile.seek(0)

    return (os.WEXITSTATUS(retcode), retfile)
