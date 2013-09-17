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
args.argparser.add_argument("--strategy", choices=["hybrid", "explicit", "cbmc"],
    default="hybrid", help="the synthesis strategy")
args.argparser.add_argument("--synth-strategy",
    choices=["default", "hybrid", "explicit", "cbmc"], default="default",
    help="the synthesis strategy")
args.argparser.add_argument("--verif-strategy",
    choices=["default", "hybrid", "explicit", "cbmc"], default="default",
    help="the synthesis strategy")

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
  gccargs = []
  scratchfile = None

  def __init__(self, sz, width, consts, verif=False):
    nargs = args.args.args
    nres = args.args.res
    pwidth = log2(sz + consts + nargs - 1)
    pwidth = max(pwidth, 1)
    ewidth = width/4
    mwidth = width - ewidth - 1
    self.verif = verif

    self.scratchfile = tempfile.NamedTemporaryFile(suffix=".c",
        delete=not args.args.keeptemps)

    genericargs = [
        "-I%s" % args.args.interpreter,
        "-DSZ=%d" % sz,
        "-DWIDTH=%d" % width,
        "-DMWIDTH=%d" % mwidth,
        "-DNARGS=%d" % nargs,
        "-DNRES=%d" % nres,
        "-DCONSTS=%d" % consts,
        "-DPWIDTH=%d" % pwidth,
        os.path.join(args.args.interpreter, "exec.c"),
        os.path.join(args.args.interpreter, "exclude.c"),
        self.scratchfile.name,
        args.args.checker
      ]

    if args.args.float:
      genericargs.insert(0, "-DFLOAT")

    if verif:
      self.cbmcargs = [args.args.cbmc,
          os.path.join("cbmc", "verif.c")] + genericargs
      self.gccargs = [args.args.gcc, "-DSEARCH", "-std=c99",
          os.path.join("explicit", "verif.c")] + genericargs
    else:
      self.cbmcargs = [args.args.cbmc, "-DSYNTH",
          os.path.join("cbmc", "synth.c")] + genericargs
      self.gccargs = [args.args.gcc, "-DSEARCH", "-std=c99",
          os.path.join("explicit", "synth.c")] + genericargs

    if not args.args.noslice:
      self.cbmcargs.append("--slice-formula")


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

    if strategy in ("cbmc", "hybrid"):
      cbmcfile = tempfile.NamedTemporaryFile(delete=not args.args.keeptemps)
      cbmcproc = subprocess.Popen(self.cbmcargs, stdout=cbmcfile,
          preexec_fn=os.setpgrp)
      procs.append((cbmcproc, cbmcfile, "cbmc"))

    if strategy in ("explicit", "hybrid"):
      ofile = tempfile.NamedTemporaryFile(delete=False)
      self.gccargs += ["-o", ofile.name, "-lm"]

      ofile.close()

      if args.args.verbose > 1:
        subprocess.call(self.gccargs)
      else:
        with open(os.devnull, "w") as fnull:
          subprocess.call(self.gccargs, stdout=fnull, stderr=fnull)

      explicitout = tempfile.NamedTemporaryFile(delete=not args.args.keeptemps)
      explicitproc = subprocess.Popen([ofile.name], stdout=explicitout,
          preexec_fn=os.setpgrp)
      procs.append((explicitproc, explicitout, "explicit"))

    (finished, retcode) = os.wait()
    perf.end("checker")

    retfile = None

    for (proc, outfile, checker) in procs:
      if proc.pid == finished:
        retfile = outfile
        perf.inc(checker)

        if args.args.verbose > 0:
          print "Fastest checker: %s" % checker
      else:
        os.killpg(proc.pid, signal.SIGKILL)
        proc.wait()

    if args.args.strategy in ("explicit", "hybrid") and not args.args.keeptemps:
      os.remove(ofile.name)


    retfile.seek(0)

    return (os.WEXITSTATUS(retcode), retfile)
