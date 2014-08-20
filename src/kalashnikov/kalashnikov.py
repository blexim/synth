#!/usr/bin/python

import subprocess
import tempfile
import re
import itertools
import random
import time
import sys
import signal
import perfcounters as perf
import args

from checker import Checker
from prog import Prog, str2ints

HEADER = '\033[95m'
OKBLUE = '\033[94m'
OKGREEN = '\033[92m'
WARNING = '\033[93m'
FAIL = '\033[91m'
ENDC = '\033[0m'
BOLD = "\033[1m"
UP = "\033[1A"

RED = "\033[31m"

cexre = re.compile('cex_args={(.*?)}')

args.argparser.add_argument("--name", default=None, type=str,
    help="benchmark name")

args.argparser.add_argument("--seqlen", "-s", default=1, type=int,
    help="minimum length of code sequence to synthesise")
args.argparser.add_argument("--seqlim", "-S", default=16, type=int,
    help="maximum length of code sequence to synthesise")

args.argparser.add_argument("--args", "-a", default=1, type=int,
    help="number of arguments to function")
args.argparser.add_argument("--res", "-r", default=1, type=int,
    help="number of returns")
args.argparser.add_argument("--evars", "-V", default=0, type=int,
    help="number of existentially quantified arguments")
args.argparser.add_argument("--progs", "-P", default=1, type=int,
    help="number of programs to synthesise")

args.argparser.add_argument("--float", "-f", default=False, action="store_const",
    const=True,
    help="Synthesize floating point programs")

args.argparser.add_argument("--consts", "-c", default=-1, type=int,
    help="number of constants to synthesize")

args.argparser.add_argument("--wordwidth", "-w", default=3, type=int,
    help="initial word size to use")
args.argparser.add_argument("--targetwordwidth", "-W", default=32, type=int,
    help="target word size to use")

args.argparser.add_argument("--exclude", "-e", default=0, type=int,
    help="maximum number of sequences to exclude")

args.argparser.add_argument("--exhaustive", "-E", default=False,
    action="store_const", const=True,
    help="exhaustively search for all sequences")

args.argparser.add_argument("--tests", "-t", default=16, type=int,
    help="number of test vectors to generate")

args.argparser.add_argument("--verbose", "-v", action='count',
    help="increase verbosity")

args.argparser.add_argument("--timeout", "-T", default=1800, type=int,
    help="time limit")

args.argparser.add_argument("--seed", default=None, type=int,
    help="random seed")

args.argparser.add_argument("checker", nargs="+",
    help="code to check the function we synthesise")

class TimeoutError(Exception):
  pass

def alarm_handler(signum, frame):
  raise TimeoutError()

signal.signal(signal.SIGALRM, alarm_handler)

def synth(tests, exclusions, width, codelen, nconsts):
  """
  Synthesise a new code sequence.
  """

  perf.start("synth")

  bmc = Checker(codelen, width, nconsts)

  testfile = open("/tmp/testvectors", "w")


  # Write the test inputs...
  bmc.write(r"""
#include "synth.h"

void tests(solution_t *solution) {
  word_t input[NARGS];
""")

  testfile.write("%d\n" % len(tests))

  #random.shuffle(tests)
  for x in tests:
    for i in xrange(len(x)):
      bmc.write("  input[%d] = %d;\n" % (i, x[i]))

    bmc.write("  test(solution, input);\n\n")

    testfile.write(" ".join(str(d) for d in x) + "\n")

  testfile.close()

  # Now we're going to list each of the programs we
  # already know are wrong...

  for soln in exclusions:
    ops = soln.ops
    parms = soln.params
    consts = soln.consts
    evars = soln.evars

    bmc.write("  assume(!(")

    for i in xrange(len(ops)):
      if i != 0:
        bmc.write(" && ")

      bmc.write("solution->prog.ops[%d] == %d " % (i, ops[i]))
      bmc.write("&& solution->prog.params[%d] == %d && solution->prog.params[%d] == %d && solution->prog.params[%d] == %d" %
          (3*i, parms[3*i], 3*i+1, parms[3*i+1], 3*i+1, parms[3*i+2]))

    for i in xrange(len(consts)):
      bmc.write("&& solution->prog.consts[%d] == %d" %
          (i, consts[i]))

    for i in xrange(len(evars)):
      bmc.write("&& solution->evars[%d] == %d" %
          (i, evars[i]))

    bmc.write("));\n")

  bmc.write("}\n")

  try:
    (retcode, output) = bmc.run()
  finally:
    perf.end("synth")

  prog = None

  if retcode == 10:
    # A counterexample was found -- extract the code sequence from it!
    prog = Prog()
    prog.parse(output)

  return prog

def verif(prog, checker, width, codelen):
  """
  Verify that a sequence is correct & extract a new test vector if it's not."
  """

  perf.start("verify")

  sz = max(len(o) for o in prog.ops)
  bmc = Checker(sz, width, len(prog.consts[0]), verif=True)
  solfile = open("/tmp/solution", "w")

  solfile.write(" ".join("0x%x" % (x & 0xffffffff) for x in prog.evars) + "\n")

  for i in xrange(args.args.progs):
    nops = len(prog.ops[i])
    solfile.write("%d\n" % nops)

    for j in xrange(nops):
      solfile.write("%d %d %d %d\n" % (prog.ops[i][j],
                                       prog.params[i][3*j],
                                       prog.params[i][3*j + 1],
                                       prog.params[i][3*j + 2]))

    nconsts = len(prog.consts[i])

    for j in xrange(nconsts):
      solfile.write("0x%x\n" % (prog.consts[i][j] & 0xffffffff))

  solfile.close()

  cfile = open("/tmp/exec.c", "w")
  cfile.write(r"""
#include "synth.h"
#include "heaplib.h"

volatile int execok;

void exec(prog_t *prog, word_t args[NARGS], word_t res[NRES]) {
""")

  for i in xrange(args.args.progs):
    cfile.write(r"""
  if (prog == &solution.progs[%d]) {
  """ % i)

    for j in xrange(sz):
      cfile.write("  res[%d] = 0;\n" % j)

    cfile.write(prog.prog2str(prog.ops[i], prog.params[i], prog.consts[i], executable=True))
    cfile.write("\n  }\n")
  cfile.write("}")
  cfile.close()


  bmc.write(r"""
#include "synth.h"

solution_t solution = {
  {
""")

  for i in xrange(args.args.progs):
    bmc.write(r"""
  {
    %d,
    { %s },
    { %s },
    { %s },
  },
""" % (len(prog.ops[i]),
       ", ".join(str(o) for o in prog.ops[i]),
       ", ".join(str(p) for p in prog.params[i]),
       ", ".join(str(c) for c in prog.consts[i])))

  bmc.write(r"""
  },

  { %s }
};
""" % (", ".join(str(e) for e in prog.evars)))

  try:
    (retcode, output) = bmc.run()
  finally:
    perf.end("verify")

  cex = None

  if retcode == 10:
    # We got a counterexample -- extract a new test case from it
    for l in output:
      mx = cexre.search(l)

      if mx:
        cex = tuple(str2ints(mx.group(1)))
  else:
    # No counterexample -- this sequence is correct!
    pass

  return cex

def kalashnikov(checker):
  codelen = args.args.seqlen
  wordlen = args.args.wordwidth
  targetwordlen = args.args.targetwordwidth
  n = 1
  tests = gentests(wordlen, codelen)
  exclusions = []
  correct = []
  starttime = time.time()
  seqlim = args.args.seqlim
  nconsts = 0

  signal.alarm(args.args.timeout)

  if args.args.consts >= 0:
    nconsts = args.args.consts

  if args.args.exhaustive:
    numsearch = -1
  else:
    numsearch = 1

  perf.start()

  while codelen <= seqlim and len(correct) != numsearch:
    sys.stdout.flush()

    perf.inc("iterations")

    if not args.args.verbose:
      endtime = time.time()
      elapsed = endtime-starttime

      print ("Iteration: " + BOLD + RED + "%d" + ENDC) % n
      print ("Code sequence length: " + BOLD + RED + "%d/%d" + ENDC) % (codelen,
          args.args.seqlim)
      print ("Word width: " + BOLD + RED + "%d/%d" + ENDC) % (wordlen,
          targetwordlen)
      print ("Excluded sequences: " + BOLD + RED + "%d/%d" + ENDC) % (
          len(exclusions), args.args.exclude)
      print ("Test vectors: " + BOLD + RED + "%d" + ENDC) % len(tests)
      print ("Constants: " + BOLD + RED + "%d" + ENDC) % nconsts
      print ("Elapsed time: " + BOLD + RED + "%.02fs" + ENDC) % elapsed

      if args.args.exhaustive:
        print ("Correct sequences: " + BOLD + RED + "%d" + ENDC) %(
            len(correct))
        print UP*2 + "\r"

      print UP*8 + "\r"
      sys.stdout.flush()

    if args.args.verbose > 0:
      print correct

    n += 1

    if args.args.verbose > 1:
      print "Test vectors: %s" % str(tests)

    prog = synth(tests, exclusions+correct, wordlen, codelen, nconsts)

    if prog == None:
      if args.args.verbose > 0:
        print "No sequence possible!"

      if args.args.consts < 0 and nconsts < codelen:
        nconsts += 1
      else:
        codelen += 1

        if args.args.consts < 0:
          nconsts = 0

      exclusions = []

      if args.args.verbose > 0:
        print "Increasing constants to %d\n" % nconsts
        print "Increasing sequence length to %d\n" % codelen

      continue

    if args.args.verbose > 0:
      print str(prog)

    test = verif(prog, checker, wordlen, codelen)

    if test is None:
      if args.args.verbose > 0:
        print "Correct for wordlen=%d" % wordlen

      if wordlen == targetwordlen:
        correct.append(prog)
        continue

      test = verif(prog, checker, targetwordlen, codelen)
      if test is None:
        if args.args.verbose > 0:
          print "Also correct for wordlen=%d!" % targetwordlen

        correct.append(prog)
        continue

      if args.args.verbose > 0:
        print "Trying to generalize..."

      newprog = generalize(prog, checker, wordlen, targetwordlen, tests, codelen)

      if newprog:
        if args.args.verbose > 1:
          print "Generalized!"

        correct.append(newprog)

        prog = newprog
        continue

      if args.args.verbose > 0:
        print "Couldn't generalize :-("

      if len(exclusions) < args.args.exclude:
        if args.args.verbose > 0:
          print "Excluding current sequence"

        perf.inc("exclusions")
        exclusions.append(prog)
      else:
        exclusions = []
        wordlen *= 2

        if wordlen > targetwordlen:
          wordlen = targetwordlen

        tests = gentests(wordlen, codelen)
        tests = list(set(tests))

        if args.args.verbose > 0:
          print "Increasing wordlen to %d" % wordlen
    else:
      if args.args.verbose > 0:
        print "Fails for %s\n" % str(test)

      tests.append(test)

  perf.end()
  endtime = time.time()
  elapsed = endtime-starttime

  print "\n"*6
  print "Finished in %0.2fs\n" % elapsed
  
  for prog in correct:
    print str(prog)
    print ""

def expand(x, narrow, wide):
  if args.args and args.args.verbose > 1:
    print "Expanding 0x%x from %d to %d bits" % (x, narrow, wide)

  ret = [x, 0]

  if x == (1 << narrow) - 1:
    ret.append((1 << wide) - 1)

  if x == 1 << (narrow - 1):
    ret.append(1 << (wide - 1))

  if x == (1 << (narrow - 1)) - 1:
    ret.append((1 << (wide - 1)) - 1)

  lo = x & 1
  hi = (x >> (narrow - 1)) & 1
  mid = (x & ((1 << (narrow - 1)) - 1)) >> 1

  midwidth = narrow - 2
  z = 0
  q = 0

  while q < wide:
    z <<= midwidth
    z |= mid
    q += midwidth

  z <<= 1
  z |= lo

  z &= (1 << wide) - 1

  z &= (1 << (wide - 1)) - 1
  z |= (hi << (wide - 1))

  #ret = [x, z]
  #ret = [x]

  if x == (1 << narrow):
    #ret.append(1 << wide)
    pass

  if x == narrow:
    #ret.append(wide)
    pass

  if x == narrow-1:
    #ret.append(wide-1)
    pass

  if x == narrow+1:
    #ret.append(wide+1)
    pass

  ret.append(x << (wide-narrow))

  y = x
  z = narrow

  while z < wide:
    q = wide-z

    if q >= narrow:
      y <<= narrow
      y |= x
      z += narrow
    else:
      y <<= q
      w = (x >> (narrow-q))
      w &= ((1 << q) - 1)
      y |= w
      z = wide

  ret.append(y)

  if args.args and args.args.verbose > 1:
    print "Expanded to %s" % str(ret)

  return sorted(list(set(ret)), reverse=True)

def generalize(prog, checker, width, targetwidth, tests, codelen):
  perf.start("generalize")
  ret = heuristic_generalize(prog, checker, width, targetwidth, codelen)
  perf.end("generalize")

  return ret


def heuristic_generalize(prog, checker, width, targetwidth, codelen):
  """
  Use heuristics to guess constants with which to generalize the program.
  """

  expansions = []

  for i in xrange(len(prog.consts)):
    for j in xrange(len(prog.consts[i])):
      if prog.const_used(i, j):
        expanded = expand(prog.consts[i][j], width, targetwidth)
      else:
        expanded = [0]

      expansions.append(expanded)

  for i in xrange(len(prog.evars)):
    expanded = expand(prog.evars[i], width, targetwidth)
    expansions.append(expanded)

  for newconsts in itertools.product(*expansions):
    const_lists = []
    n = 0 

    for i in xrange(len(prog.consts)):
      l = []

      for j in xrange(len(prog.consts[i])):
        l.append(newconsts[n])
        n += 1

      const_lists.append(l)

    newevars = []
    for i in xrange(len(prog.evars)):
      newevars.append(newconsts[n])
      n += 1

    newprog = Prog(prog.ops, prog.params, const_lists, newevars)

    if args.args.verbose > 1:
      print "Trying %s" % (str(newprog))

    if verif(newprog, checker, targetwidth, codelen) is None:
      return newprog

  return None

def ispow2(x):
  return x != 0 and ((x & (x-1)) == 0)

def gentests(wordlen, codelen):
  numargs = args.args.args
  numtests = min(args.args.tests, 2**(wordlen * numargs))
  numslice = int(numtests**(1.0/numargs))
  k = 3

  # See if we can exhaust the state space...
  if (1 << (wordlen*numargs)) <= numtests:
    slices = [range(1 << wordlen) for i in xrange(numargs)]
    return list(itertools.product(*slices))

  # This is fairly arbitrary...  Above 2^30, we're too big to fit
  # in a python int, so we're just going to randomly generate test
  # vectors & rely on the fact that our state space is large enough
  # that we're unlikely to generate the same vector twice.
  if wordlen < 30:
    vecs = xrange(2**wordlen)
    slices = [random.sample(vecs, numslice) for i in xrange(numargs)]
  else:
    slices = []

    for i in xrange(numargs):
      thisslice = [random.randint(0, (2**wordlen) - 1)
                    for j in xrange(numslice)]
      thisslice = [(x & ((1 << k) - 1)) | i for x in thisslice]

      slices.append(thisslice)

  return list(itertools.product(*slices))

if __name__ == '__main__':
  args.args = args.argparser.parse_args()

  random.seed()

  if args.args.seed is None:
    args.args.seed = random.randint(0, 100000)

  print "Using seed: %d" % args.args.seed

  random.seed(args.args.seed)

  try:
    kalashnikov(args.args.checker)
  except TimeoutError:
    perf.inc("timeout")
    print "\n"*7 + "Timeout"

  if args.args.verbose > 0:
    perf.summary()
