#!/usr/bin/python

import os
import sys
import copy
import tempfile
import splitter

def prove_terminates(filename):
  splitfile = tempfile.NamedTemporaryFile(mode='w', suffix='.c', delete=False)
  (id_map, has_nested) = splitter.split(filename, splitfile)
  nids = len(id_map)
  varnames = ' '.join(id_map[k] for k in xrange(nids))

  splitfile.close()

  os.system(("./kalashnikov.py " +
             "%s ../../papers/termination/experiments/benchmarks/unranking.c " +
             "--synth-strategy=genetic " +
             "--fastverif=false -c=1 -keepfrac=15 -mutprob=0.25 -newfrac=2 -popsize=500 " +
             "-recombprob=0.05 -tourneysize=10 -w=3 " +
             "-a%d --evars %d --varnames %s --resnames I --seed=1337 " +
             "%s") % 
              (splitfile.name,
                nids,
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

  prove_terminates(sys.argv[1])
