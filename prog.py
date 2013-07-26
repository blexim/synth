#!/usr/bin/python

import re
import perfcounters as perf
import args

opsre = re.compile('ops={(.*?)}')
parmsre = re.compile('params={(.*?)}')
constsre = re.compile('consts={(.*?)}')

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
    12: "<=",
    13: "<"
}

unops = {
    4: "-",
    5: "~"
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

  def __init__(self, ops=[], params=[], consts=[]):
    self.ops = ops
    self.params = params
    self.consts = consts

  def parse(self, output):
    for l in output:
      mops = opsre.search(l)
      mparams = parmsre.search(l)
      mconsts = constsre.search(l)

      if mops:
        self.ops = str2ints(mops.group(1))

      if mparams:
        self.params = str2ints(mparams.group(1))

      if mconsts:
        self.consts = str2ints(mconsts.group(1))

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
    # [(op0, param0, param1, 1), (op1, param2, param3, 2), ... ]
    insts = zip(self.ops, self.params[::2], self.params[1::2],
        xrange(1, len(self.ops) + 1))
    strinsts = []

    for (op, p1, p2, idx) in insts:
      if op in binops:
        strinsts.append("t%d = %s %s %s" % (idx, self.strarg(p1), binops[op],
          self.strarg(p2)))
      elif op in unops:
        strinsts.append("t%d = %s%s" % (idx, unops[op], self.strarg(p1)))
      else:
        raise "Couldn't parse instruction: (%d, %d, %d)" % (op, p1, p2)

    return '\n'.join(strinsts)
