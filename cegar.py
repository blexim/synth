#!/usr/bin/python

import subprocess
import tempfile
import re
import itertools


CBMC = "/home/matt/cbmc-svn/trunk/src/cbmc/cbmc"
TESTS = [0]

opsre = re.compile('ops={(.*?)}')
parmsre = re.compile('[^x]parms={(.*?)}')
xparmsre = re.compile('xparms={(.*?)}')

cexxre = re.compile('counterexample_x=(\d+)')
cexyre = re.compile('counterexample_y=(\d+)')

codelen = 1
codelenlim = 15

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

def parse(s):
  ret = []

  for w in s.split(','):
    w = w.strip()
    w = w.replace('u', '')

    ret.append(int(w))

  return ret

def prettyarg(p, x):
  if x == 1:
    return hex(p)
  else:
    if p == 0:
      return 'x'
    else:
      return 't%d' % p

def prettyprint(prog):
  (ops, parms, xparms) = prog

  i = 0

  while i < len(ops):
    opcode = ops[i]
    p1 = parms[2*i]
    p2 = parms[2*i + 1]
    x1 = xparms[2*i]
    x2 = xparms[2*i + 1]

    a1 = prettyarg(p1, x1)
    a2 = prettyarg(p2, x2)

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

    print "t%d = %s" % (i+1, rhs)

    i += 1

  print "res = t%d" % (len(ops))

def synth(checker, tests, width):
  """
  Synthesise a new code sequence.
  """

  # First we need to write the test inputs to a file...
  testfile = tempfile.NamedTemporaryFile(suffix='.c', delete=False)

  testfile.write("#include \"synth.h\"\n\n")
  testfile.write("void tests(prog_t prog) {\n")

  for x in tests:
    testfile.write("  test(%d, prog);\n" % x)

  testfile.write("}\n")
  testfile.flush()

  # OK cool, now let's run CBMC
  cbmcfile = tempfile.NamedTemporaryFile()
  args = [CBMC, "-I.", "-DSZ=%d" % codelen, "-DWIDTH=%d" % width, "-DSYNTH",
      "--slice-formula", checker, testfile.name, "synth.c", "exec.c"]

  retcode = subprocess.call(args, stdout=cbmcfile)

  cbmcfile.seek(0)

  ops = None
  parms = None
  xparms = None

  if retcode == 10:
    # A counterexample was found -- extract the code sequence from it!

    for l in cbmcfile.readlines():
      mops = opsre.search(l)
      mparms = parmsre.search(l)
      mxparms = xparmsre.search(l)

      if mops:
        ops = parse(mops.group(1))

      if mparms:
        parms = parse(mparms.group(1))

      if mxparms:
        xparms = parse(mxparms.group(1))

    return (ops, parms, xparms)

  return None

def verif(prog, checker, width):
  """
  Verify that a sequence is correct & extract a new test vector if it's not."
  """

  progfile = tempfile.NamedTemporaryFile(suffix='.c')

  (ops, parms, xparms) = prog

  progfile.write("#include \"synth.h\"\n\n")
  progfile.write("op_t ops[] = { %s };\n" %
      ', '.join(str(s) for s in ops))
  progfile.write("word_t parms[] = { %s };\n" %
      ', '.join(str(p) for p in parms))
  progfile.write("bit_t xparms[] = { %s };\n" %
      ', '.join(str(x) for x in xparms))
  progfile.write("prog_t prog = { ops, parms, xparms };\n")
  progfile.flush()

  args = [CBMC, "-I.", "-DSZ=%d" % codelen, "-DWIDTH=%d" % width,
          checker, progfile.name, "exec.c", "verif.c"]
  cbmcfile = tempfile.NamedTemporaryFile()
  retcode = subprocess.call(args, stdout=cbmcfile)

  cbmcfile.seek(0)


  if retcode == 10:
    # We got a counterexample -- extract a new test case from it

    x = 0
    y = 0

    for l in cbmcfile.readlines():
      mx = cexxre.search(l)

      if mx:
        x = int(mx.group(1))

    return x

  # No counterexample -- this sequence is correct!
  return None

def cegar(checker):
  global codelen
  global codelenlim

  wordlen = 2
  targetwordlen = 32
  n = 1
  finished = False
  tests = TESTS

  while not finished:
    print "Iteration %d:" % n
    n += 1

    prog = synth(checker, tests, wordlen)
    prog = optimize(prog, wordlen)

    if prog == None:
      print "No sequence possible!"

      if codelen < codelenlim:
        codelen += 1
        #tests = TESTS
        print "Increasing sequence length to %d\n" % codelen
        continue

    prettyprint(prog)
    print ""

    test = verif(prog, checker, wordlen)

    if test is None:
      print "Correct for wordlen=%d" % wordlen

      if wordlen == targetwordlen:
        print "Done!"
        finished = True
        break

      test = verif(prog, checker, targetwordlen)
      if test is None:
        print "Also correct for wordlen=%d!" % targetwordlen
        finished = True
        break

      tests.append(test)

      print "Trying to generalize..."
      newprog = generalize(prog, checker, wordlen, targetwordlen, tests)

      if newprog:
        print "Generalized to:"
        prettyprint(newprog)
        finished = True
        print "\nDone!"
        break

      print "Couldn't generalize :-("

      wordlen *= 2

      if wordlen > targetwordlen:
        wordlen = targetwordlen

      tests = [test]

      print "Increasing wordlen to %d" % wordlen
    else:
      print "Fails for %s\n" % hex(test)
      tests.append(test)

def expand(x, narrow, wide):
  if x == 1 or x == 0:
    return [x]

  if x == (1 << narrow):
    return [x, 1 << wide]

  if x == narrow:
    return [x, wide]

  if x == narrow-1:
    return [x, wide-1]

  if x == narrow+1:
    return [x, wide+1]

  ret = [x]
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

  return ret

def generalize(prog, checker, width, targetwidth, tests):
  return heuristic_generalize(prog, checker, width, targetwidth)

def heuristic_generalize(prog, checker, width, targetwidth):
  """
  Use heuristics to guess constants with which to generalize the program.
  """

  (ops, parms, xparms) = prog
  expansions = []

  for i in xrange(len(parms)):
    if xparms[i] == 0:
      expansions.append([parms[i]])
    else:
      expanded = expand(parms[i], width, targetwidth)
      expansions.append(expanded)

  for newparms in itertools.product(*expansions):
    newprog = (ops, list(newparms), xparms)

    if verif(newprog, checker, targetwidth) is None:
      return newprog

  return None

def sat_generalize(prog, checker, width, targetwidth, tests):
  """
  Try to generalize a program which is correct for a word width < the
  width we want, to a program which is correct for the full width.
  """

  # Our basic technique is to find constants in the program and try to
  # extend them to a wider wordsize...

  (ops, parms, xparms) = prog

  # First we need to write the test inputs to a file...
  testfile = tempfile.NamedTemporaryFile(suffix='.c', delete=False)

  testfile.write("#include \"synth.h\"\n\n")
  testfile.write("void tests(prog_t prog) {\n")

  for i in xrange(len(ops)):
    testfile.write("  __CPROVER_assume(prog.ops[%d] == %d);\n" % (i, ops[i]))

    testfile.write("  __CPROVER_assume(prog.xparms[%d] == %d);\n" %
        (2*i, xparms[2*i]))
    testfile.write("  __CPROVER_assume(prog.xparms[%d] == %d);\n" %
        (2*i + 1, xparms[2*i + 1]))

    if xparms[2*i] == 0:
      testfile.write("  __CPROVER_assume(prog.parms[%d] == %d);\n" %
          (2*i, parms[2*i]))

    if xparms[2*i+1] == 0:
      testfile.write("  __CPROVER_assume(prog.parms[%d] == %d);\n" %
          (2*i+1, parms[2*i+1]))

  for t in tests:
    testfile.write("  test(%d, prog);\n" % t)

  testfile.write("}\n")
  testfile.flush()

  # OK cool, now let's run CBMC
  cbmcfile = tempfile.NamedTemporaryFile()
  args = [CBMC, "-I.", "-DSZ=%d" % codelen, "-DWIDTH=%d" % targetwidth,
      "--slice-formula", checker, testfile.name, "synth.c", "exec.c"]

  retcode = subprocess.call(args, stdout=cbmcfile)

  cbmcfile.seek(0)

  ops = None
  parms = None
  xparms = None

  if retcode == 10:
    # A counterexample was found -- extract the code sequence from it!

    for l in cbmcfile.readlines():
      mops = opsre.search(l)
      mparms = parmsre.search(l)
      mxparms = xparmsre.search(l)

      if mops:
        ops = parse(mops.group(1))

      if mparms:
        parms = parse(mparms.group(1))

      if mxparms:
        xparms = parse(mxparms.group(1))

    newprog = (ops, parms, xparms)

    if verif(newprog, checker, targetwidth) is None:
      return newprog

  return None

def ispow2(x):
  return x != 0 and ((x & (x-1)) == 0)

def log2(x):
  ret = -1

  while x:
    ret += 1
    x >>= 1

  return ret

def optimize(prog, wordlen):
  """
  Simple keyhole optimizations...
  """

  if prog is None:
    return None

  (ops, parms, xparms) = prog

  for i in xrange(len(ops)):
    op = ops[i]
    p1 = parms[i*2]
    p2 = parms[i*2+1]
    x1 = xparms[i*2]
    x2 = xparms[i*2+1]

    if op == MUL and x2 == 1 and p2 == ((1 << wordlen) - 1):
      # Replace y = x * -1 with y = -x
      ops[i] = NEG
    elif op == MUL and x2 == 1 and ispow2(p2):
      # Replace y = x * 2**k with y = x << k
      ops[i] = SHL
      parms[i*2+1] = log2(p2)
    elif op == DIV and x2 == 1 and ispow2(p2):
      # Replace y = x / 2**k with y = x >> k
      ops[i] = LSHR
      parms[i*2+1] = log2(p2)

  return (ops, parms, xparms)

if __name__ == '__main__':
  import sys

  checker = sys.argv[1]

  if len(sys.argv) > 2:
    codelen = int(sys.argv[2])

  if len(sys.argv) > 3:
    codelenlim = int(sys.argv[3])

  cegar(checker)
