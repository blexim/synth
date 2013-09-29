#!/usr/bin/python

import sys
import os

benchmarks11 = [1, 2, 3, 4, 5, 6, 7, 8,
    9, 13, 17, 18, 20, 22, 23, 24]
benchmarks21 = [10, 11, 12, 14, 15, 16]
benchmarks31 = [19]
benchmarks41 = [21]

wordoverrides = {4:4, 24: 8}

numbenchmarks = 24

def runbenchmarks():
  for i in xrange(1, numbenchmarks+1):
    print i

    if i in benchmarks11:
      args = 1
      res = 1
    elif i in benchmarks21:
      args = 2
      res = 1
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

    cmd = ("./cegar.py -a%d -r%d -w%d -v specs/p%d.c > benchmarks/%d.out" %
        (args, res, word, i, i))

    print cmd
    os.system(cmd)

if __name__ == '__main__':
  runbenchmarks()
