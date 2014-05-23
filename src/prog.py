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
    for l in output:
      mops = opsre.search(l)
      mparams = parmsre.search(l)
      mconsts = constsre.search(l)
      mevars = evarsre.search(l)

      if mops:
        self.ops = str2ints(mops.group(1))

      if mparams:
        self.params = str2ints(mparams.group(1))

      if mconsts:
        self.consts = str2ints(mconsts.group(1))

      if mevars:
        self.evars = str2ints(mevars.group(1))

  def strarg(self, p):
    if p < len(self.consts):
      return hex(self.consts[p])
    else:
      p -= len(self.consts)

      if p < args.args.args:
        return 'a%d' % (p+1)
      else:
        return 't%d' % (p - args.args.args + 1)

  def __str__(self):
    # List comprehension trickery to generate a list like:
    # [(op0, param0, param1, param2, 1), (op1, param3, param4, param5, 2), ... ]
    insts = zip(self.ops, self.params[::3], self.params[1::3], self.params[2::3],
        xrange(1, len(self.ops) + 1))
    strinsts = []

    for (op, p1, p2, p3, idx) in insts:
      if op in binops:
        strinsts.append("t%d = %s %s %s" % (idx, self.strarg(p1), binops[op],
          self.strarg(p2)))
      elif op in unops:
        strinsts.append("t%d = %s%s" % (idx, unops[op], self.strarg(p1)))
      elif op in ternops:
        strinsts.append("t%d = %s(%s, %s, %s)" % (idx, ternops[op], self.strarg(p1),
                                                  self.strarg(p2), self.strarg(p3)))
      else:
        raise Exception("Couldn't parse instruction: (%d, %d, %d, %d)" %
            (op, p1, p2, p3))

    if self.evars:
      ret = 'Evars: %s\n' % ', '.join(self.evars)
    else:
      ret = ''

    return ret + '\n'.join(strinsts)
