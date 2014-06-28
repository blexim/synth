#!/usr/bin/python

import re
import perfcounters as perf
import args

args.argparser.add_argument("--varnames", nargs="*", default=[],
    help="variable names")
args.argparser.add_argument("--resnames", nargs="*", default=[],
    help="result names")

opsre = re.compile('ops={(.*?)}')
parmsre = re.compile('params={(.*?)}')
constsre = re.compile('consts={(.*?)}')
evarsre = re.compile('evars={(.*?)}')

binops = {
    0: "%s + %s",
    1: "%s - %s",
    2: "%s * %s",
    3: "%s / %s",
    5: "%s & %s",
    6: "%s | %s",
    7: "%s ^ %s",
    9: "%s << %s",
    10: "%s >> %s",
    11: "((sword_t) %s) >> ((sword_t) %s)",
    12: "%s == %s",
    13: "%s != %s",
    14: "%s <= %s",
    15: "%s < %s",
    16: "((sword_t) %s) <= ((sword_t) %s)",
    17: "((sword_t) %s) < ((sword_t) %s)",
    18: "%s %% %s",
    19: "!%s || %s",    # Implies
    20: "min(%s, %s)",
    21: "max(%s, %s)",
    23: "f+(%s, %s)",
    24: "f-(%s, %s)",
    25: "f*(%s, %s)",
    26: "f/(%s, %s)"
}

revbinops = { v: k for (k, v) in binops.items() }

unops = {
    4: "-%s",
    8: "~%s"
}

revunops = { v: k for (k, v) in unops.items() }

ternops = {
    22: "%s ? %s : %s"
}

revternops = { v: k for (k, v) in ternops.items() }

def str2ints(s):
  ret = []

  if not s:
    return []

  for w in s.split(','):
    w = w.strip()
    w = w.replace('u', '')

    ret.append(int(w))

  return ret

class Prog(object):
  ops = []
  params = []
  consts = []
  evars = []

  def __init__(self, ops=[], params=[], consts=[], evars=[]):
    self.ops = ops
    self.params = params
    self.consts = consts
    self.evars = evars

  def parse(self, output):
    self.ops = []
    self.params = []
    self.consts = []
    self.evars = []

    for l in output:
      mops = opsre.search(l)
      mparams = parmsre.search(l)
      mconsts = constsre.search(l)
      mevars = evarsre.search(l)

      if mops:
        self.ops.append(str2ints(mops.group(1)))

      if mparams:
        self.params.append(str2ints(mparams.group(1)))

      if mconsts:
        self.consts.append(str2ints(mconsts.group(1)))

      if mevars:
        self.evars = str2ints(mevars.group(1))

  def argname(self, p):
    return "args[%d]" % p

    if len(args.args.varnames) < args.args.args:
      return 'a%d' % (p+1)
    else:
      return args.args.varnames[p]

  def tempname(self, seqlen, idx):
    return "res[%d]" % (seqlen - idx - 1)

    residx = idx - seqlen + args.args.res

    if residx >= 0:
      if residx < len(args.args.resnames):
        return args.args.resnames[residx]
      else:
        return "res%d" % (residx + 1)
    else:
      return "t%d" % (idx + 1)


  def strarg(self, p, seqlen, consts):
    if p < len(consts):
      return hex(consts[p])
    else:
      p -= len(consts)

      if p < args.args.args:
        return self.argname(p)
      else:
        return self.tempname(seqlen, p - args.args.args)

  def prog2str(self, ops, params, consts):
    # List comprehension trickery to generate a list like:
    # [(op0, param0, param1, param2, 0), (op1, param3, param4, param5, 1), ... ]
    insts = zip(ops, params[::3], params[1::3], params[2::3],
        xrange(0, len(ops)))
    strinsts = []

    sliced = self.slice(ops, params, consts)

    for (op, p1, p2, p3, idx) in insts:
      if idx not in sliced:
        continue

      lhs = self.tempname(len(ops), idx)

      if op in binops:
        rhs = binops[op] % (
            self.strarg(p1, len(ops), consts),
            self.strarg(p2, len(ops), consts))
      elif op in unops:
        rhs = unops[op] % (
            self.strarg(p1, len(ops), consts))
      elif op in ternops:
        rhs = ternops[op] % (
            self.strarg(p1, len(ops), consts),
            self.strarg(p2, len(ops), consts),
            self.strarg(p3, len(ops), consts))
      else:
        raise Exception("Couldn't parse instruction: (%d, %d, %d, %d)" %
            (op, p1, p2, p3))

      strinsts.append("%s = %s;" % (lhs, rhs))

    return '\n'.join(strinsts)

  def slice(self, ops, params, consts):
    return range(len(ops))

    ret = set([len(ops) - i - 1 for i in xrange(args.args.res)])

    for i in xrange(len(ops) - 1, -1, -1):
      if i not in ret:
        continue

      op = ops[i]

      if op in unops:
        nargs = 1 
      elif op in binops:
        nargs = 2 
      elif op in ternops:
        nargs = 3 

      ps = [params[i*3 + j] for j in xrange(nargs)]

      for p in ps:
        if p >= args.args.args + len(consts):
          temp_idx = p - args.args.args - len(consts)
          ret.add(temp_idx)

    return ret


  def __str__(self):
    if self.evars:
      ret = 'Evars: %s\n' % ', '.join(str(e) for e in self.evars)
    else:
      ret = ''

    for i in xrange(len(self.ops)):
      ret += "Program %d:\n" % i
      ret += self.prog2str(self.ops[i], self.params[i], self.consts[i])
      ret += "\n"

    return ret
