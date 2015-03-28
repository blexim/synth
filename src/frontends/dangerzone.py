#!/usr/bin/python

import os
import sys
import copy
import tempfile
import splitter

kalashnikov_dir = os.environ["KALASHNIKOVDIR"]

def prove_danger(filename):
  splitfile = tempfile.NamedTemporaryFile(mode='w', suffix='.c', delete=False)
  (id_map, has_nested, nondet) = splitter.split(filename, splitfile)
  nids = len(id_map)
  varnames = (' '.join(id_map[k] for k in xrange(nids)) + ' ' +
              ' '.join("0" for i in xrange(nids)))

  splitfile.close()

  cmd = (("kalashnikov.py " +
             "%s %s/tests/loops/danger.c " +
             "-P3 " +
             "--seed=1337 " +
             "--strategy=evolve -a%d --evars %d --varnames %s --nondet=%d -w=3 " +
             "%s") % 
              (splitfile.name,
                kalashnikov_dir,
                nids,
                nids,
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

  sys.exit(prove_danger(sys.argv[1]))
