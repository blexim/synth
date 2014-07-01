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
  varnames = (' '.join(id_map[k] for k in xrange(nids)) + ' ' +
              ' '.join("0" for i in xrange(nids)))

  splitfile.close()

  cmd = (("./kalashnikov.py " +
             "%s ../../papers/termination/experiments/benchmarks/combined.c " +
             "-P3 " +
             "--seed=1337 " +
             "--synth-strategy=genetic -a%d --evars %d --varnames %s --resnames I " +
             "--fastverif=false -c=1 -keepfrac=15 -mutprob=0.1 -newfrac=2 -popsize=500 " +
             "-recombprob=0.05 -tourneysize=10 -w=3 " +
             "%s") % 
              (splitfile.name,
                nids*2,
                nids,
                varnames,
                ' '.join(sys.argv[2:])))

  print cmd
  os.system(cmd)

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

  try:
    os.unlink("/tmp/testvectors")
  except:
    pass

  sys.exit(prove_terminates(sys.argv[1]))
