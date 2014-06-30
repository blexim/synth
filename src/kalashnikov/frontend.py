#!/usr/bin/python

import os
import sys
import copy
import tempfile
import splitter

def prove_terminates(filename):
  splitfile = tempfile.NamedTemporaryFile(mode='w', suffix='.c', delete=False)
  id_map = splitter.split(filename, splitfile)
  nids = len(id_map)
  varnames = ' '.join(id_map[k] for k in xrange(nids))

  splitfile.close()

  return os.system(("./kalashnikov.py " +
             "%s ../../papers/termination/experiments/benchmarks/ranking.c " +
             "-P2 " +
             "--synth-strategy=genetic -c1 -s2 --seed=1337 -w4 -a%d --varnames %s --resnames I " +
             "%s") % 
              (splitfile.name,
                nids,
                varnames,
                ' '.join(sys.argv[2:])))

if __name__ == '__main__':
  import sys

  try:
    os.unlink("/tmp/geneticsynth")
  except:
    pass

  try:
    os.unlink("/tmp/annealsynth")
  except:
    pass

  sys.exit(prove_terminates(sys.argv[1]))
