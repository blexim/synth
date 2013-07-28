#!/usr/bin/python

import tempfile
import subprocess
import perfcounters as perf
import args
import os

#args.argparser.add_argument("--cbmc", default="cbmc", type=str,
#    help="path to CBMC")
#args.argparser.add_argument("--interpreter", "-I", default="interpreter",
#    type=str, help="path to interpreter")
#args.argparser.add_argument("--keeptemps", "-k", default=False,
#    action="store_const", const=True,
#    help="keep temporary files")
#args.argparser.add_argument("--noslice", default=False,
#    action="store_const", const=True,
#    help="do not slice formula")

def log2(x):
  i = 0
  extra = 0

  while x > 1:
    if x & 1:
      extra = 1

    x >>= 1
    i += 1

  return i+extra

class Cbmc(object):
  cbmcargs = []
  scratchfile = None

  def __init__(self, sz, width, consts, *extra):
    nargs = args.args.args
    pwidth = log2(sz + consts + nargs - 1)
    pwidth = max(pwidth, 1)

    self.scratchfile = tempfile.NamedTemporaryFile(suffix=".c",
        delete=not args.args.keeptemps)

    self.cbmcargs = [
        args.args.cbmc,
        "-I%s" % args.args.interpreter,
        "-DSZ=%d" % sz,
        "-DWIDTH=%d" % width,
        "-DNARGS=%d" % nargs,
        "-DCONSTS=%d" % consts,
        "-DPWIDTH=%d" % pwidth,
        self.scratchfile.name
      ]

    if not args.args.noslice:
      self.cbmcargs.append("--slice-formula")

    def fixc(f):
      # There's a race condition here, and I don't care.
      if f.endswith(".c") and not os.path.exists(f):
        p = os.path.join(args.args.interpreter, f)

        if os.path.exists(p):
          return p

      return f

    extra = [fixc(f) for f in extra]
    self.cbmcargs += extra

    self.write = self.scratchfile.write

  def run(self):
    cbmcfile = tempfile.NamedTemporaryFile(delete=not args.args.keeptemps)

    self.scratchfile.flush()

    perf.start("cbmc")
    retcode = subprocess.call(self.cbmcargs, stdout=cbmcfile)
    perf.end("cbmc")

    cbmcfile.seek(0)

    return (retcode, cbmcfile)
