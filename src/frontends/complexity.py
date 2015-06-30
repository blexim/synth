#!/usr/bin/python

import os
import sys
import copy
import tempfile
import splitter

kalashnikov_dir = os.environ["KALASHNIKOVDIR"]

def complexity(filename):
  splitfile = tempfile.NamedTemporaryFile(mode='w', suffix='.c', delete=False)
  (id_map, has_nested, nondet) = splitter.split(filename, splitfile)
  nids = len(id_map)
  varnames = (' '.join(id_map[k] for k in xrange(nids)) + ' bound')

  splitfile.close()

  cmd = (("kalashnikov.py " +
             "%s %s/tests/loops/complexity.c " +
             "-P2 " +
             "--seed=1337 " +
             #"--strategy=evolve " +
             "-a%d --evars 0 --varnames %s --nondet=%d -w=3 " +
             "%s") % 
              (splitfile.name,
                kalashnikov_dir,
                nids + 1,
                varnames,
                nondet,
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

  sys.exit(complexity(sys.argv[1]))
