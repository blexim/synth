#!/usr/bin/python

import re
import perfcounters as perf
import args

opsre = re.compile('ops={(.*?)}')
parmsre = re.compile('params={(.*?)}')
constsre = re.compile('consts={(.*?)}')

ops = {
    0: "+",
    1: "-",
    2: "*",
    3: "/",
    4: "unary -",
    5: "&",
    6: "|",
    7: "^",
    8: "~",
    9: "<<",
    10: ">>",
    11: ">>>",
    12: "<=",
    13: "<",
    14: "PUSH",
    15: "DUP",
    16: "SWAP"
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
    if p < args.args.args:
      return 'a%d' % (p+1)
    elif p < args.args.args + len(self.consts):
      return hex(self.consts[p - args.args.args])
    else:
      print "ERROR"

  def __str__(self):
    insts = zip(self.ops, self.params, xrange(1, len(self.ops) + 1))
    strinsts = []

    for (op, p, idx) in insts:
      if op == 14:
        strinsts.append("PUSH %s" % (self.strarg(p)))
      elif op in ops:
        strinsts.append(ops[op])
      else:
        raise Exception("Couldn't parse instruction: (%d, %d, %d)" %
            (op, p1, p2))

    return '\n'.join(strinsts)
