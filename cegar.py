#!/usr/bin/python

import subprocess
import tempfile
import re
import itertools
import random
import time
import sys
import perfcounters as perf
import cbmc
import args

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

args.argparser.add_argument("--seqlen", "-s", default=1, type=int,
    help="minimum length of code sequence to synthesise")
args.argparser.add_argument("--seqlim", "-S", default=16, type=int,
    help="maximum length of code sequence to synthesise")

args.argparser.add_argument("--args", "-a", default=1, type=int,
    help="number of arguments to function")

args.argparser.add_argument("--consts", "-c", default=-1, type=int,
    help="number of constants to synthesize")

args.argparser.add_argument("--wordwidth", "-w", default=3, type=int,
    help="initial word size to use")
args.argparser.add_argument("--targetwordwidth", "-W", default=32, type=int,
    help="target word size to use")

args.argparser.add_argument("--exclude", "-e", default=2, type=int,
    help="maximum number of sequences to exclude")

args.argparser.add_argument("--exhaustive", "-E", default=False,
    action="store_const", const=True,
    help="exhaustively search for all sequences")

args.argparser.add_argument("--tests", "-t", default=16, type=int,
    help="number of test vectors to generate")

args.argparser.add_argument("--verbose", "-v", action='count',
    help="increase verbosity")

args.argparser.add_argument("checker",
    help="code to check the function we synthesise")

def log2(x):
  i = 0
  extra = 0

  while x > 1:
    if x & 1:
      extra = 1

    x >>= 1
    i += 1

  return i+extra

def synth(checker, tests, exclusions, width, codelen, nconsts):
  """
  Synthesise a new code sequence.
  """

  perf.start("synth")

  bmc = cbmc.cbmc(codelen, width, nconsts,
      "-DSYNTH", "synth.c", "exec.c", "exclude.c", checker)

  # Write the test inputs...
  bmc.write(r"""
#include "synth.h"

void tests(prog_t *prog) {
  word_t input[NARGS];
""")

  random.shuffle(tests)
  for x in tests:
    for i in xrange(len(x)):
      bmc.write("  input[%d] = %d;\n" % (i, x[i]))

    bmc.write("  test(input, prog);\n\n")

  # Now we're going to list each of the programs we
  # already know are wrong...

  for (ops, parms, consts) in exclusions:
    bmc.write("  __CPROVER_assume(!(")

    for i in xrange(len(ops)):
      if i != 0:
        bmc.write(" && ")

      bmc.write("prog->ops[%d] == %d " % (i, ops[i]))
      bmc.write("&& prog->params[%d] == %d && prog->params[%d] == %d" %
          (2*i, parms[2*i], 2*i+1, parms[2*i+1]))

    for i in xrange(len(consts)):
      bmc.write("&& prog->consts[%d] == %d" %
          (i, consts[i]))

    bmc.write("));\n")

  bmc.write("}\n")

  (retcode, output) = bmc.run()

  prog = None

  if retcode == 10:
    # A counterexample was found -- extract the code sequence from it!
    prog = Prog()
    prog.parse(output)

  perf.end("synth")
  return prog

def verif(prog, checker, width, codelen):
  """
  Verify that a sequence is correct & extract a new test vector if it's not."
  """

  perf.start("verify")

  bmc = cbmc.cbmc(codelen, width, len(prog.consts),
      checker, "exec.c", "verif.c")

  bmc.write(r"""
#include "synth.h"

prog_t prog = {
  { %s },
  { %s },
  { %s },
};
""" % (", ".join(str(o) for o in prog.ops),
       ", ".join(str(p) for p in prog.params),
       ", ".join(str(c) for c in prog.consts)))

  (retcode, output) = bmc.run()

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

  perf.end("verify")
  return cex

def cegar(checker):
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
    perf.summary(args.args)

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

    if len(tests) > 3*codelen and False:
      tests = gentests(wordlen, codelen)


    if args.args.verbose > 1:
      print "Test vectors: %s" % str(tests)

    prog = synth(checker, tests, exclusions+correct, wordlen, codelen, nconsts)
    #prog = optimize(prog, wordlen)

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
      #tests = gentests(wordlen, codelen)

      if args.args.verbose > 0:
        print "Increasing constants to %d\n" % nconsts
        print "Increasing sequence length to %d\n" % codelen

      continue

    if args.args.verbose > 0:
      print str(prog)
      #prettyprint(prog)

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

      #tests.append(test)

      if args.args.verbose > 0:
        print "Trying to generalize..."

      newprog = generalize(prog, checker, wordlen, targetwordlen, tests, codelen)

      if newprog:
        if args.args.verbose > 1:
          print "Generalized!"

        perf.inc("exclusions")
        exclusions.append(prog)

        correct.append(newprog)

        prog = newprog
        continue

      if args.args.verbose > 0:
        print "Couldn't generalize :-("

      if len(exclusions) < args.args.exclude:
        if args.args.verbose > 0:
          print "Excluding current sequence"

        exclusions.append(prog)
      else:
        exclusions = []
        wordlen += 1

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
    #prettyprint(prog)
    print ""

def expand(x, narrow, wide):
  if args.args and args.args.verbose > 1:
    print "Expanding %x from %d to %d bits" % (x, narrow, wide)

  ret = [x]

  if x == (1 << narrow):
    ret.append(1 << wide)

  if x == narrow:
    ret.append(wide)

  if x == narrow-1:
    ret.append(wide-1)

  if x == narrow+1:
    ret.append(wide+1)

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

  return list(set(ret))

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
    expanded = expand(prog.consts[i], width, targetwidth)
    expansions.append(expanded)

  for newconsts in itertools.product(*expansions):
    newprog = Prog(prog.ops, prog.params, list(newconsts))

    if args.args.verbose > 1:
      print "Trying %s" % (str(newprog))

    if verif(newprog, checker, targetwidth, codelen) is None:
      return newprog

  return None

def ispow2(x):
  return x != 0 and ((x & (x-1)) == 0)

def optimize(prog, wordlen):
  """
  Simple keyhole optimizations...
  """

  perf.start("optimize")

  if prog is None:
    perf.end("optimize")
    return None

  (ops, parms, consts) = prog

  for i in xrange(len(ops)):
    op = ops[i]
    p1 = parms[i*2]
    p2 = parms[i*2+1]
    x1 = consts[i*2]
    x2 = consts[i*2+1]

    if op == MUL and x2 == 1 and p2 == ((1 << wordlen) - 1):
      # Replace y = x * -1 with y = -x
      perf.inc("optimizations")
      ops[i] = NEG
    elif op == MUL and x2 == 1 and ispow2(p2):
      # Replace y = x * 2**k with y = x << k
      perf.inc("optimizations")
      ops[i] = SHL
      parms[i*2+1] = log2(p2)
    elif op == DIV and x2 == 1 and ispow2(p2):
      # Replace y = x / 2**k with y = x >> k
      perf.inc("optimizations")
      ops[i] = LSHR
      parms[i*2+1] = log2(p2)

  perf.end("optimize")
  return (ops, parms, consts)

def gentests(wordlen, codelen):
  perf.start("gentests")

  numargs = args.args.args
  numtests = min(args.args.tests, 2**(wordlen * numargs))
  numslice = int(numtests**(1.0/numargs))

  if (1 << (wordlen*numargs)) <= numtests:
    slices = [range(1 << wordlen) for i in xrange(numargs)]
    return list(itertools.product(*slices))

  maxneg = 0x80000000
  maxpos = 0x7fffffff

  vecs = [1, 0, -1, maxneg, maxpos, maxneg+1, maxpos-1, 0x01234567,
      0x89abcdef, -2, 2, -3, 3, -64, 64, -5, -31415]

  vecs = xrange(2**wordlen)

  slices = [random.sample(vecs, numslice) for i in xrange(numargs)]

  #slices = [[0] for i in xrange(numargs)]

  perf.end("gentests")
  return list(itertools.product(*slices))

if __name__ == '__main__':
  args.args = args.argparser.parse_args()

  random.seed()

  cegar(args.args.checker)
