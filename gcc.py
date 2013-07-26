#!/usr/bin/python

import tempfile
import subprocess
import perfcounters as perf
import args
import os

args.argparser.add_argument("--gcc", default="gcc", type=str,
    help="path to GCC")
args.argparser.add_argument("--searcher", default="searcher", type=str,
    help="path to searcher code")

def log2(x):
  i = 0
  extra = 0

  while x > 1:
    if x & 1:
      extra = 1

    x >>= 1
    i += 1

  return i+extra

class Gcc(object):
  gccargs = []
  scratchfile = None
  ofile = None

  def __init__(self, sz, width, consts, *extra):
    nargs = args.args.args
    pwidth = log2(sz + consts + nargs - 1)
    pwidth = max(pwidth, 1)

    self.scratchfile = tempfile.NamedTemporaryFile(suffix=".c",
        delete=not args.args.keeptemps)

    self.ofile = tempfile.NamedTemporaryFile(delete=False)

    self.gccargs = [
        args.args.gcc,
        "-I%s" % args.args.interpreter,
        "-DSZ=%d" % sz,
        "-DWIDTH=%d" % width,
        "-DNARGS=%d" % nargs,
        "-DCONSTS=%d" % consts,
        "-DPWIDTH=%d" % pwidth,
        "-O3",
        "-std=c99",
        "-o",
        self.ofile.name,
        self.scratchfile.name
      ]

    def fixc(f):
      # There's a race condition here, and I don't care.
      if f.endswith(".c") and not os.path.exists(f):
        p = os.path.join(args.args.interpreter, f)

        if os.path.exists(p):
          return p

        p = os.path.join(args.args.searcher, f)

        if os.path.exists(p):
          return p

      return f

    extra = [fixc(f) for f in extra]
    self.gccargs += extra

    self.write = self.scratchfile.write

  def run(self):
    self.scratchfile.flush()
    self.ofile.close()

    perf.start("gcc")

    with open(os.devnull, "w") as fnull:
      retcode = subprocess.call(self.gccargs, stdout=fnull, stderr=fnull)

    perf.end("gcc")

    outputfile = tempfile.NamedTemporaryFile(delete=not args.args.keeptemps)

    perf.start("compiled")
    retcode = subprocess.call([self.ofile.name], stdout=outputfile)
    perf.end("compiled")

    if not args.args.keeptemps:
      os.remove(self.ofile.name)

    outputfile.seek(0)

    return (retcode, outputfile)
