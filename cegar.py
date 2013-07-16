#!/usr/bin/python

import subprocess
import tempfile
import re
import itertools
import random
import argparse
import time
import sys
import perfcounters as perf

CBMC = "/home/matt/cbmc-svn/trunk/src/cbmc/cbmc"

HEADER = '\033[95m'
OKBLUE = '\033[94m'
OKGREEN = '\033[92m'
WARNING = '\033[93m'
FAIL = '\033[91m'
ENDC = '\033[0m'
BOLD = "\033[1m"
UP = "\033[1A"

RED = "\033[31m"


opsre = re.compile('ops={(.*?)}')
parmsre = re.compile('params={(.*?)}')
constsre = re.compile('consts={(.*?)}')

cexre = re.compile('cex_args={(.*?)}')

argparser = argparse.ArgumentParser(
    description="Synthesise a loop free program")
argparser.add_argument("--seqlen", "-s", default=1, type=int,
    help="minimum length of code sequence to synthesise")
argparser.add_argument("--seqlim", "-S", default=16, type=int,
    help="maximum length of code sequence to synthesise")

argparser.add_argument("--args", "-a", default=1, type=int,
    help="number of arguments to function")

argparser.add_argument("--consts", "-c", default=-1, type=int,
    help="number of constants to synthesize")

argparser.add_argument("--wordwidth", "-w", default=3, type=int,
    help="initial word size to use")
argparser.add_argument("--targetwordwidth", "-W", default=32, type=int,
    help="target word size to use")

argparser.add_argument("--exclude", "-e", default=2, type=int,
    help="maximum number of sequences to exclude")

argparser.add_argument("--exhaustive", "-E", default=False,
    action="store_const", const=True,
    help="exhaustively search for all sequences")

argparser.add_argument("--tests", "-t", default=16, type=int,
    help="number of test vectors to generate")

argparser.add_argument("--verbose", "-v", action='count',
    help="increase verbosity")

argparser.add_argument("--hint", default=None, type=str,
    help="hints to use for synthesis")

argparser.add_argument("checker",
    help="code check the function we synthesise")

args = None

PLUS=0
MINUS=1
MUL=2
DIV=3
NEG=4
AND=5
OR=6
XOR=7
NOT=8
SHL=9
LSHR=10
ASHR=11
LE=12
LT=13

def log2(x):
  i = 0
  extra = 0

  while x > 1:
    if x & 1:
      extra = 1

    x >>= 1
    i += 1

  return i+extra

def parse(s):
  ret = []

  for w in s.split(','):
    w = w.strip()
    w = w.replace('u', '')

    ret.append(int(w))

  return ret

def prettyarg(p, consts):
  if p < len(consts):
    return hex(consts[p])
  else:
    p -= len(consts)

    if p < args.args:
      return 'a%d' % (p+1)
    else:
      return 't%d' % (p - args.args + 1)

def prettyprint(prog):
  (ops, parms, consts) = prog

  print prog

  i = 0

  while i < len(ops):
    opcode = ops[i]
    p1 = parms[2*i]
    p2 = parms[2*i + 1]

    a1 = prettyarg(p1, consts)
    a2 = prettyarg(p2, consts)

    if opcode == PLUS:
      rhs = "%s + %s" % (a1, a2)
    elif opcode == MINUS:
      rhs = "%s - %s" % (a1, a2)
    elif opcode == MUL:
      rhs = "%s * %s" % (a1, a2)
    elif opcode == DIV:
      rhs = "%s / %s" % (a1, a2)
    elif opcode == NEG:
      rhs = "-%s" % a1
    elif opcode == AND:
      rhs = "%s & %s" % (a1, a2)
    elif opcode == OR:
      rhs = "%s | %s" % (a1, a2)
    elif opcode == XOR:
      rhs = "%s ^ %s" % (a1, a2)
    elif opcode == NOT:
      rhs = "~%s" % a1
    elif opcode == SHL:
      rhs = "%s << %s" % (a1, a2)
    elif opcode == LSHR:
      rhs = "%s >> %s" % (a1, a2)
    elif opcode == ASHR:
      rhs = "%s >>> %s" % (a1, a2)
    elif opcode == LE:
      rhs = "%s <= %s" % (a1, a2)
    elif opcode == LT:
      rhs = "%s < %s" % (a1, a2)
    elif opcode == GE:
      rhs = "%s >= %s" % (a1, a2)
    elif opcode == GT:
      rhs = "%s > %s" % (a1, a2)

    print "t%d = %s" % (i+1, rhs)

    i += 1

  print "res = t%d" % (len(ops))

def synth(checker, tests, exclusions, width, codelen, nconsts):
  """
  Synthesise a new code sequence.
  """

  global args

  perf.start("synth")

  # First we need to write the test inputs to a file...
  testfile = tempfile.NamedTemporaryFile(suffix='.c', delete=False)

  testfile.write("#include \"synth.h\"\n\n")
  testfile.write("void tests(prog_t *prog) {\n")
  testfile.write("  word_t input[NARGS];\n\n");

  random.shuffle(tests)
  for x in tests:
    for i in xrange(len(x)):
      testfile.write("  input[%d] = %d;\n" % (i, x[i]))

    testfile.write("  test(input, prog);\n\n")

  # Now we're going to list each of the programs we
  # already know are wrong...

  for (ops, parms, consts) in exclusions:
    testfile.write("  __CPROVER_assume(!(")

    for i in xrange(len(ops)):
      if i != 0:
        testfile.write(" && ")

      testfile.write("prog->ops[%d] == %d " % (i, ops[i]))
      testfile.write("&& prog->params[%d] == %d && prog->params[%d] == %d" %
          (2*i, parms[2*i], 2*i+1, parms[2*i+1]))

    for i in xrange(len(consts)):
      testfile.write("&& prog->consts[%d] == %d" %
          (i, consts[i]))

    testfile.write("));\n")

  testfile.write("}\n")
  testfile.flush()

  pwidth = log2(codelen + nconsts + args.args - 1)
  pwidth = max(pwidth, 1)

  # OK cool, now let's run CBMC
  cbmcfile = tempfile.NamedTemporaryFile(delete=False)
  cbmcargs = [CBMC, "-I.", "-DSZ=%d" % codelen, "-DWIDTH=%d" % width, "-DSYNTH",
      "-DNARGS=%d" % args.args,
      "-DCONSTS=%d" % nconsts, "-DPWIDTH=%d" % pwidth,
      "--slice-formula", checker, testfile.name, "synth.c", "exec.c",
      "exclude.c"]

  if args.hint:
    cbmcargs += ["-DHINT", args.hint]

  perf.start("cbmc")
  retcode = subprocess.call(cbmcargs, stdout=cbmcfile)
  perf.end("cbmc")

  cbmcfile.seek(0)

  ops = None
  parms = None
  consts = []

  if retcode == 10:
    # A counterexample was found -- extract the code sequence from it!

    for l in cbmcfile.readlines():
      mops = opsre.search(l)
      mparms = parmsre.search(l)
      mconsts = constsre.search(l)

      if mops:
        ops = parse(mops.group(1))

      if mparms:
        parms = parse(mparms.group(1))

      if mconsts:
        consts = parse(mconsts.group(1))

    perf.end("synth")
    return (ops, parms, consts)

  perf.end("synth")
  return None

def verif(prog, checker, width, codelen, nconsts):
  """
  Verify that a sequence is correct & extract a new test vector if it's not."
  """

  perf.start("verify")

  progfile = tempfile.NamedTemporaryFile(suffix='.c', delete=False)

  (ops, parms, consts) = prog

  progfile.write("#include \"synth.h\"\n\n")
  progfile.write("prog_t prog = {\n")
  progfile.write("  { %s },\n" %
      ', '.join(str(s) for s in ops))
  progfile.write("  { %s },\n" %
      ', '.join(str(p) for p in parms))
  progfile.write("  { %s }\n" %
      ', '.join(str(x) for x in consts))
  progfile.write("};")
  progfile.flush()

  pwidth = log2(codelen + nconsts + args.args - 1)
  pwidth = max(pwidth, 1)

  cbmcargs = [CBMC, "-I.", "-DSZ=%d" % codelen, "-DWIDTH=%d" % width,
          "-DNARGS=%d" % args.args,
          "-DCONSTS=%d" % nconsts, "-DPWIDTH=%d" % pwidth,
          checker, progfile.name, "exec.c", "verif.c"]
  cbmcfile = tempfile.NamedTemporaryFile()

  perf.start("cbmc")
  retcode = subprocess.call(cbmcargs, stdout=cbmcfile)
  perf.end("cbmc")

  cbmcfile.seek(0)


  if retcode == 10:
    # We got a counterexample -- extract a new test case from it
    x = 0

    for l in cbmcfile.readlines():
      mx = cexre.search(l)

      if mx:
        x = tuple(parse(mx.group(1)))

    perf.end("verify")
    return x

  # No counterexample -- this sequence is correct!
  perf.end("verify")
  return None

def cegar(checker):
  codelen = args.seqlen
  wordlen = args.wordwidth
  targetwordlen = args.targetwordwidth
  n = 1
  tests = gentests(wordlen, codelen)
  exclusions = []
  correct = []
  starttime = time.time()
  seqlim = args.seqlim
  nconsts = 0

  if args.consts >= 0:
    nconsts = args.consts

  if args.exhaustive:
    numsearch = -1
  else:
    numsearch = 1

  perf.start()

  while codelen <= seqlim and len(correct) != numsearch:
    sys.stdout.flush()

    perf.inc("iterations")
    perf.summary(args)

    if not args.verbose:
      endtime = time.time()
      elapsed = endtime-starttime

      print ("Iteration: " + BOLD + RED + "%d" + ENDC) % n
      print ("Code sequence length: " + BOLD + RED + "%d/%d" + ENDC) % (codelen,
          args.seqlim)
      print ("Word width: " + BOLD + RED + "%d/%d" + ENDC) % (wordlen,
          targetwordlen)
      print ("Excluded sequences: " + BOLD + RED + "%d/%d" + ENDC) % (
          len(exclusions), args.exclude)
      print ("Test vectors: " + BOLD + RED + "%d" + ENDC) % len(tests)
      print ("Constants: " + BOLD + RED + "%d" + ENDC) % nconsts
      print ("Elapsed time: " + BOLD + RED + "%.02fs" + ENDC) % elapsed

      if args.exhaustive:
        print ("Correct sequences: " + BOLD + RED + "%d" + ENDC) %(
            len(correct))
        print UP*2 + "\r"

      print UP*8 + "\r"
      sys.stdout.flush()

    if args.verbose > 0:
      print correct

    n += 1

    if len(tests) > 3*codelen and False:
      tests = gentests(wordlen, codelen)


    if args.verbose > 1:
      print "Test vectors: %s" % str(tests)

    prog = synth(checker, tests, exclusions+correct, wordlen, codelen, nconsts)
    #prog = optimize(prog, wordlen)

    if prog == None:
      if args.verbose > 0:
        print "No sequence possible!"

      if args.consts < 0 and nconsts < codelen:
        nconsts += 1
      else:
        codelen += 1

        if args.consts < 0:
          nconsts = 0

      exclusions = []
      #tests = gentests(wordlen, codelen)

      if args.verbose > 0:
        print "Increasing constants to %d\n" % nconsts
        print "Increasing sequence length to %d\n" % codelen

      continue

    if args.verbose > 0:
      prettyprint(prog)

    test = verif(prog, checker, wordlen, codelen, nconsts)

    if test is None:
      if args.verbose > 0:
        print "Correct for wordlen=%d" % wordlen

      if wordlen == targetwordlen:
        correct.append(prog)
        continue

      test = verif(prog, checker, targetwordlen, codelen, nconsts)
      if test is None:
        if args.verbose > 0:
          print "Also correct for wordlen=%d!" % targetwordlen

        correct.append(prog)
        continue

      #tests.append(test)

      if args.verbose > 0:
        print "Trying to generalize..."

      newprog = generalize(prog, checker, wordlen, targetwordlen, tests, codelen)

      if newprog:
        if args.verbose > 1:
          print "Generalized!"

        perf.inc("exclusions")
        exclusions.append(prog)

        correct.append(newprog)

        prog = newprog
        continue

      if args.verbose > 0:
        print "Couldn't generalize :-("

      if len(exclusions) < args.exclude:
        if args.verbose > 0:
          print "Excluding current sequence"

        exclusions.append(prog)
      else:
        exclusions = []
        wordlen += 1

        if wordlen > targetwordlen:
          wordlen = targetwordlen

        tests = gentests(wordlen, codelen)
        tests = list(set(tests))

        if args.verbose > 0:
          print "Increasing wordlen to %d" % wordlen
    else:
      if args.verbose > 0:
        print "Fails for %s\n" % str(test)

      tests.append(test)

  perf.end()
  endtime = time.time()
  elapsed = endtime-starttime

  print "\n"*6
  print "Finished in %0.2fs\n" % elapsed
  
  for prog in correct:
    prettyprint(prog)
    print ""

def expand(x, narrow, wide):
  if args and args.verbose > 1:
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

  if args and args.verbose > 1:
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

  (ops, parms, consts) = prog
  expansions = []

  for i in xrange(len(consts)):
    expanded = expand(consts[i], width, targetwidth)
    expansions.append(expanded)

  for newconsts in itertools.product(*expansions):
    newprog = (ops, parms, list(newconsts))

    if args.verbose > 1:
      print "Trying %s" % (str(newprog))

    if verif(newprog, checker, targetwidth, codelen, len(consts)) is None:
      return newprog

  return None

def sat_generalize(prog, checker, width, targetwidth, tests):
  """
  Try to generalize a program which is correct for a word width < the
  width we want, to a program which is correct for the full width.
  """

  # Our basic technique is to find constants in the program and try to
  # extend them to a wider wordsize...

  (ops, parms, consts) = prog

  # First we need to write the test inputs to a file...
  testfile = tempfile.NamedTemporaryFile(suffix='.c', delete=False)

  testfile.write("#include \"synth.h\"\n\n")
  testfile.write("void tests(prog_t prog) {\n")

  for i in xrange(len(ops)):
    testfile.write("  __CPROVER_assume(prog.ops[%d] == %d);\n" % (i, ops[i]))

    testfile.write("  __CPROVER_assume(prog.consts[%d] == %d);\n" %
        (2*i, consts[2*i]))
    testfile.write("  __CPROVER_assume(prog.consts[%d] == %d);\n" %
        (2*i + 1, consts[2*i + 1]))

    if consts[2*i] == 0:
      testfile.write("  __CPROVER_assume(prog.params[%d] == %d);\n" %
          (2*i, parms[2*i]))

    if consts[2*i+1] == 0:
      testfile.write("  __CPROVER_assume(prog.params[%d] == %d);\n" %
          (2*i+1, parms[2*i+1]))

  for t in tests:
    testfile.write("  test(%d, prog);\n" % t)

  testfile.write("}\n")
  testfile.flush()

  # OK cool, now let's run CBMC
  cbmcfile = tempfile.NamedTemporaryFile()
  cbmcargs = [CBMC, "-I.", "-DSZ=%d" % codelen, "-DWIDTH=%d" % targetwidth,
      "--slice-formula", checker, testfile.name, "synth.c", "exec.c"]

  perf.start("cbmc")
  retcode = subprocess.call(cbmcargs, stdout=cbmcfile)
  perf.end("cbmc")

  cbmcfile.seek(0)

  ops = None
  parms = None
  consts = None

  if retcode == 10:
    # A counterexample was found -- extract the code sequence from it!

    for l in cbmcfile.readlines():
      mops = opsre.search(l)
      mparms = parmsre.search(l)
      mconsts = constsre.search(l)

      if mops:
        ops = parse(mops.group(1))

      if mparms:
        parms = parse(mparms.group(1))

      if mconsts:
        consts = parse(mconsts.group(1))

    newprog = (ops, parms, consts)

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

  numargs = args.args
  numtests = min(args.tests, 2**(wordlen * numargs))
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
  args = argparser.parse_args()

  random.seed()

  cegar(args.checker)
