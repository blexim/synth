#!/usr/bin/python

import sys
import re

if "--neg" in sys.argv:
  negate = True
else:
  negate = False

hre = re.compile("p cnf (\d+) (\d+)")
evarsre = re.compile("e(( \d+)+)")
avarsre = re.compile("a(( \d+)+)")

def parse_line(l):
  hm = hre.match(l)
  em = evarsre.match(l)
  am = avarsre.match(l)

  if hm:
    return ('h', [int(hm.group(1)), int(hm.group(2))])
  elif em:
    evars = em.group(1).split()[:-1]
    evars = [int(e) for e in evars]
    return ('e', evars)
  elif am:
    avars = am.group(1).split()[:-1]
    avars = [int(a) for a in avars]
    return ('a', avars)
  else:
    clause = l.split()[:-1]
    clause = [int(v) for v in clause]
    return ('c', clause)

def convert_file(fin, fout):
  fout.write(r"""
#include "synth.h"

int check(solution_t *sol, word_t args[NARGS]) {
  word_t res[NRES];
  word_t eargs[NARGS];
  int i;
  int ret = 0;

""")

  avars = []
  nevars = 0
  nefuncs = 0
  nclauses = 0

  for l in fin:
    if l[0] == 'c':
      continue

    (ty, val) = parse_line(l)

    univ = 'e' if negate else 'a'
    exist = 'a' if negate else 'e'

    if ty == 'h':
      continue
    elif ty == univ:
      idx = len(avars)

      for v in val:
        fout.write("  word_t x%d = args[%d];\n" % (v, idx))
        avars.append(v)
        idx += 1
    elif ty == exist:
      if not avars:
        idx = nevars

        for v in val:
          fout.write("  word_t x%d = sol->evars[%d];\n" % (v, idx))
          nevars += 1
          idx += 1
      else:
        fout.write(r"""
  for (i = 0; i < NARGS; i++) {
    eargs[i] = 0;
  }
""")

        for i in xrange(len(avars)):
          fout.write("  eargs[%d] = x%d;\n" % (i, avars[i]))

        idx = nefuncs

        for v in val:
          fout.write("  exec(&sol->progs[%d], eargs, res);\n" % idx)
          fout.write("  word_t x%d = res[0];\n" % v)
          nefuncs += 1
          idx += 1
    elif ty == 'c':
      pos = [v for v in val if v > 0]
      neg = [-v for v in val if v < 0]

      if negate:
        guard = ' && '.join(["!x%d" % v for v in pos] +
                            ["x%d" % v for v in neg])
      else:
        guard = ' || '.join(["x%d" % v for v in pos] +
                            ["!x%d" % v for v in neg])


      if guard:
        fout.write("  if (%s) ret += 1;\n" % guard)
        nclauses += 1

  fout.write(r"""
  return ret;
}
""")

  print "%d evars" % nevars
  print "%d functions" % nefuncs
  print "%d universals" % len(avars)
  print "%d clauses" % nclauses

if __name__ == '__main__':
  fin = open(sys.argv[1])
  fout = open(sys.argv[2], "w")

  convert_file(fin, fout)

  fin.close()
  fout.close()
