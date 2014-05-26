#!/usr/bin/python

import re
import perfcounters as perf
import args

opsre = re.compile('ops={(.*?)}')
parmsre = re.compile('params={(.*?)}')
constsre = re.compile('consts={(.*?)}')
evarsre = re.compile('evars={(.*?)}')

binops = {
    0: "+",
    1: "-",
    2: "*",
    3: "/",
    5: "&",
    6: "|",
    7: "^",
    9: "<<",
    10: ">>",
    11: ">>>",
    12: "=",
    13: "!=",
    14: "<=",
    15: "<",
    16: "s<=",
    17: "s<",
    18: "%",
    19: "==>",
    20: "MIN",
    21: "MAX",
    23: "f+",
    24: "f-",
    25: "f*",
    26: "f/"
}

unops = {
    4: "-",
    8: "~"
}

ternops = {
    22: "ITE"
}

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

  def strarg(self, p, consts):
    if p < len(consts):
      return hex(consts[p])
    else:
      p -= len(consts)

      if p < args.args.args:
        return 'a%d' % (p+1)
      else:
        return 't%d' % (p - args.args.args + 1)

  def prog2str(self, ops, params, consts):
    # List comprehension trickery to generate a list like:
    # [(op0, param0, param1, param2, 1), (op1, param3, param4, param5, 2), ... ]
    insts = zip(ops, params[::3], params[1::3], params[2::3],
        xrange(1, len(ops) + 1))
    strinsts = []

    for (op, p1, p2, p3, idx) in insts:
      if op in binops:
        strinsts.append("t%d = %s %s %s" % (idx, self.strarg(p1, consts), binops[op],
          self.strarg(p2, consts)))
      elif op in unops:
        strinsts.append("t%d = %s%s" % (idx, unops[op], self.strarg(p1, consts)))
      elif op in ternops:
        strinsts.append("t%d = %s(%s, %s, %s)" % (idx, ternops[op], self.strarg(p1, consts),
                                                  self.strarg(p2, consts), self.strarg(p3, consts)))
      else:
        raise Exception("Couldn't parse instruction: (%d, %d, %d, %d)" %
            (op, p1, p2, p3))

    return '\n'.join(strinsts)

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
