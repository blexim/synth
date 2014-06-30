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
args.argparser.add_argument("--lib", default="lib",
    type=str, help="path to library")
args.argparser.add_argument("--searcher", default="searcher",
    type=str, help="path to searcher")
args.argparser.add_argument("--keeptemps", "-k", default=False,
    action="store_const", const=True,
    help="keep temporary files")
args.argparser.add_argument("--noslice", default=False,
    action="store_const", const=True,
    help="do not slice formula")
args.argparser.add_argument("--strategy",
    choices=["all", "evolve", "explicit", "genetic", "anneal", "cbmc"],
    default="all", help="the overall strategy")
args.argparser.add_argument("--synth-strategy",
    choices=["default", "all", "anneal", "evolve", "explicit", "genetic", "cbmc"],
    default="default", help="the synthesis strategy")
args.argparser.add_argument("--verif-strategy",
    choices=["default", "explicit", "cbmc"], default="default",
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
args.argparser.add_argument("--nofastverif", default=False,
    action="store_const", const=True,
    help="don't use fast verification")

def log2(x):
  i = 0
  extra = 0

  while x > 1:
    if x & 1:
      extra = 1

    x >>= 1
    i += 1

  return i+extra

compiled = {}

class Checker(object):
  cbmcargs = []
  gccargs = {}
  scratchfile = None

  def __init__(self, sz, width, consts, verif=False):
    nargs = args.args.args
    nres = sz
    nevars = args.args.evars
    nprogs = args.args.progs
    pwidth = log2(sz + consts + nargs - 1)
    pwidth = max(pwidth, 1)
    ewidth = max(width/4, 1)
    mwidth = width - ewidth - 1

    self.sz = sz
    self.width = width

    self.verif = verif
    self.scratchfile = tempfile.NamedTemporaryFile(suffix=".c",
        delete=not args.args.keeptemps)

    genericargs = [
        "-I%s" % args.args.interpreter,
        "-I%s" % args.args.lib,
        "-DMWIDTH=%d" % mwidth,
        "-DWIDTH=%d" % width,
        "-DNARGS=%d" % nargs,
        "-DNEVARS=%d" % nevars,
        "-DNPROGS=%d" % nprogs,
        "-DCONSTS=%d" % consts,
        "-DPWIDTH=%d" % pwidth,
        os.path.join(args.args.interpreter, "exclude.c"),
        os.path.join(args.args.interpreter, "wellformed.c"),
        os.path.join(args.args.lib, "solution.c"),
        os.path.join(args.args.lib, "io.c"),
        self.scratchfile.name] + args.args.checker

    if args.args.float:
      genericargs.insert(0, "-DFLOAT")

    if not args.args.nosymmetry:
      genericargs.insert(0, "-DREMOVE_SYMMETRIC")

    if not args.args.nonops:
      genericargs.insert(0, "-DREMOVE_NOPS")

    if not args.args.noconsts:
      genericargs.insert(0, "-DREMOVE_CONST")

    if args.args.seed is not None:
      genericargs.append("-DSEED=%d" % args.args.seed)

    if verif:
      if args.args.nofastverif:
        execcfile = os.path.join("interpreter", "exec.c")
      else:
        execcfile = "/tmp/exec.c"

      self.cbmcargs = [args.args.cbmc,
          "-DSZ=%d" % sz,
          execcfile,
          "-DNRES=%d" % sz,
          os.path.join("cbmc", "verif.c"), "--32"] + genericargs

      self.gccargs["explicit"] = [args.args.gcc, "-DSEARCH", "-std=c99", "-lm",
          "-DSZ=128",
          "-DNRES=128",
          os.path.join("interpreter", "exec.c"),
          "-O3", "-g", os.path.join("explicit", "verif.c")] + genericargs
    else:
      self.cbmcargs = [args.args.cbmc, "-DSYNTH",
          "-DSZ=%d" % sz,
          os.path.join(args.args.interpreter, "exec.c"),
          os.path.join("cbmc", "synth.c")] + genericargs
      self.gccargs["explicit"] = [args.args.gcc, "-DSEARCH", "-std=c99",
          "-DSZ=%d" % sz,
          "-DNRES=%d" % sz,
          os.path.join(args.args.interpreter, "exec.c"),
          "-O3", "-g",
          os.path.join("explicit", "synth.c"), "-lm"] + genericargs
      self.gccargs["genetic"] = [args.args.gcc, "-DSEARCH", "-std=c99",
          "-DSZ=128",
          "-DNRES=128",
          os.path.join(args.args.interpreter, "exec.c"),
          "-O3", "-g",
          os.path.join("genetic", "synth.c"), "-lm"] + genericargs
      self.gccargs["anneal"] = [args.args.gcc, "-DSEARCH", "-std=c99",
          "-DSZ=%d" % sz,
          "-DNRES=%d" % sz,
          os.path.join(args.args.interpreter, "exec.c"),
          "-O3", "-g",
          os.path.join("anneal", "synth.c"), "-lm"] + genericargs


    if not args.args.noslice:
      self.cbmcargs.append("--slice-formula")

    if args.args.z3:
      self.cbmcargs.append("--z3")


    self.write = self.scratchfile.write

  def run(self):
    self.scratchfile.flush()
    perf.start("checker")
    procs = []

    strategy = None

    if args.args.verif_strategy == "default":
      args.args.verif_strategy = args.args.strategy

    if args.args.synth_strategy == "default":
      args.args.synth_strategy = args.args.strategy

    if self.verif:
      if args.args.verif_strategy in ("all", "evolve"):
        strategies = ["explicit", "cbmc"]
      else:
        strategies = [args.args.verif_strategy]
    else:
      if args.args.synth_strategy == "all":
        strategies = ["explicit", "cbmc", "genetic", "anneal"]
      elif args.args.synth_strategy == "evolve":
        strategies = ["genetic", "anneal"]
      else:
        strategies = [args.args.synth_strategy]

    try:
      if "cbmc" in strategies:
        if args.args.verbose > 1:
          print " ".join(self.cbmcargs)

        cbmcfile = tempfile.NamedTemporaryFile(delete=not args.args.keeptemps)
        cbmcproc = subprocess.Popen(self.cbmcargs, stdout=cbmcfile,
            preexec_fn=os.setpgrp)
        procs.append((cbmcproc, cbmcfile, "cbmc"))

      bins = {}

      for s in ("explicit", "genetic", "anneal"):
        if s in strategies:
          bin = self.compile(s)
          bins[s] = bin
          outfile = tempfile.NamedTemporaryFile(delete=not args.args.keeptemps)

          if args.args.verbose > 1:
            print bin.name

          proc = subprocess.Popen([bin.name], stdout=outfile,
              preexec_fn=os.setpgrp)
          procs.append((proc, outfile, s))

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

    retfile.seek(0)

    return (os.WEXITSTATUS(retcode), retfile)

  def cachable(self, (width, key)):
    return key in ("genetic-synth", "explicit-verif")

  def compile(self, name):
    global compiled

    if self.verif:
      key = (self.width, name + "-verif")
    else:
      key = (self.width, name + "-synth")

    if not self.cachable(key) or key not in compiled:
      bin = tempfile.NamedTemporaryFile(delete=not args.args.keeptemps,
                                         dir="ofiles")
      gcc = self.gccargs[name] + ["-o", bin.name, "-lm"]
      compiled[key] = bin
      bin.close()

      perf.start("gcc")
      if args.args.verbose > 1:
        print " ".join(gcc)
        subprocess.call(gcc)
      else:
        with open(os.devnull, "w") as fnull:
          subprocess.call(gcc, stdout=fnull, stderr=fnull)
      perf.end("gcc")

      return bin
    else:
      return compiled[key]
