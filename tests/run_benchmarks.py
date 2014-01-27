#!/usr/bin/python

import sys
import os

benchmarks11 = [1, 2, 3, 4, 5, 6, 7, 8,
    9, 13, 17, 18, 20, 22, 23, 24, 29]
benchmarks21 = [10, 11, 12, 14, 15, 16, 26, 27]
benchmarks22 = [28]
benchmarks31 = [19]
benchmarks41 = [21]

wordoverrides = {4:4, 24: 8}

numbenchmarks = 29

def runbenchmarks(restrict_width, flags, outdir):
  for i in xrange(1, numbenchmarks+1):
    print i

    if i in benchmarks11:
      args = 1
      res = 1
    elif i in benchmarks21:
      args = 2
      res = 1
    elif i in benchmarks22:
      args = 2
      res = 2
      flags += ' -s2'
    elif i in benchmarks31:
      args = 3
      res = 1
    elif i in benchmarks41:
      args = 4
      res = 1

    if i in wordoverrides:
      word = wordoverrides[i]
    else:
      word = 4

    if not restrict_width:
      word = 32

    cmd = ("../src/kalashnikov.py --cbmc ../bin/cbmc-glucose -a%d -r%d -w%d -v --seed 1337 -T600 %s specs/p%d.c > %s/%d.out" %
        (args, res, word, flags, i, outdir, i))

    try:
      os.mkdir(outdir)
    except:
      pass

    print cmd
    os.system(cmd)

if __name__ == '__main__':
  runbenchmarks(True, "--nonops --nosymmetry --noconst", "benchmarks/none")
  runbenchmarks(True, "--nonops --nosymmetry", "benchmarks/const")
  runbenchmarks(True, "--nonops --noconst", "benchmarks/symmetry")
  runbenchmarks(True, "--noconst --nosymmetry", "benchmarks/nops")
  runbenchmarks(True, "--nonops", "benchmarks/const+symmetry")
  runbenchmarks(True, "--noconst", "benchmarks/nops+symmetry")
  runbenchmarks(True, "--nosymmetry", "benchmarks/const+nops")
  runbenchmarks(True, "", "benchmarks/all")
  runbenchmarks(False, "", "benchmarks/nowidth")
