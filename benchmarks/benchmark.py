#!/usr/bin/python

import sys
import os

benchmarks11 = [1, 2, 3, 4, 5, 6, 7, 8,
    9, 13, 17, 18, 20, 22, 23, 24]
benchmarks21 = [10, 11, 12, 14, 15, 16,
    25]
benchmarks31 = [19, 21]

wordoverrides = {24: 8}

numbenchmarks = 25

def runbenchmarks():
  for i in xrange(1, numbenchmarks+1):
    if i in benchmarks11:
      args = 1
      res = 1
    elif i in benchmarks21:
      args = 2
      res = 1
    elif i in benchmarks31:
      args = 3
      res = 1

    if i in wordoverrides:
      word = wordoverrides[i]
    else:
      word = 5

  os.system("./cegar.py -a%d -r%s -w%d -v > benchmarks/%d.out" %
      args, res, word, i)

if __name__ == '__main__':
  runbenchmarks()
