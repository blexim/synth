#!/usr/bin/python

import os
import sys
import copy
import tempfile
import splitter

def prove_terminates(filename):
  splitfile = tempfile.NamedTemporaryFile(mode='w', suffix='.c', delete=False)
  (id_map, has_nested, nondet) = splitter.split(filename, splitfile)
  nids = len(id_map)
  varnames = ' '.join(id_map[k] for k in xrange(nids))

  splitfile.close()

  if has_nested:
    skeleton = "../../papers/termination/experiments/benchmarks/nested.c"
    nprogs = 3
    nargs = nids*2
    varnames += ' ' + ' '.join("%s\\'" % id_map[k] for k in xrange(nids))
  else:
    skeleton = "../../papers/termination/experiments/benchmarks/ranking.c"
    nprogs = 2
    nargs = nids


  cmd = (("kalashnikov.py " +
             "%s %s " +
             "-P%d  " +
             "--seed=1337 -a%d --varnames %s " +
             "--synth-strategy=genetic " +
             "-c1 " +
             "--fastverif=True " +
             "-newsize=5 " +
             "-replaceprob=0.15 " +
             "-mutprob=0.1 " +
             "-tourneysize=5 " +
             "-popsize=3000 " +
             "-w4 " +
             "%s") % 
              (splitfile.name,
                skeleton,
                nprogs,
                nargs,
                varnames,
                ' '.join(sys.argv[2:])))
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
