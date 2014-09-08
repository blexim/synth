#!/usr/bin/python

import args
import prog

def slice_prog(prog, idx):
  ret = set([idx])

  for i in xrange(idx, -1, -1):
    if i not in ret:
      continue

    op = prog.ops[idx]

    if op in unops:
      nargs = 1
    elif op in binops:
      nargs = 2
    elif op in ternops:
      nargs = 3

    params = [prog.params[i*3 + j] for j in xrange(nargs)]

    for p in params:
      if prog.is_temp(p):
        ret.insert(prog.temp_idx(p))

def prettyprint_idx(prog, idx):
  sliced = slice_prog(prog, idx)
