#!/usr/bin/python

import re
import sys

r = re.compile(r'h={[^.]*\.succ={([\d, ]*)},[^.]*\.dist={([\d, ]*)},[^.]*\.ptr={([\d, ]*)},[^.]*\.nnodes=(\d+)', flags=re.DOTALL)

cex = sys.stdin.read()

m = r.search(cex)

[succs, dists, ptrs, nnodes] = [eval(g) for g in m.groups()]

def nodeptrs(n):
  return ', '.join([ptrname(p) for p in xrange(len(ptrs)) if ptrs[p] == n])

def ptrname(p):
  if p == 0:
    return "null"
  elif p < len(sys.argv):
    return sys.argv[p]
  else:
    return "ptr_%d" % p

print "digraph {"

for n in xrange(nnodes):
  print r'node%d [label="%s"];' % (n, nodeptrs(n))

for p in xrange(len(ptrs)):
  #print r'%s [style=none];' % ptrname(p)
  pass

for n in xrange(nnodes):
  s = succs[n]
  d = dists[n]
  print r'node%d -> node%d [label="%d"];' % (n, s, d)

print ""

for p in xrange(len(ptrs)):
  n = ptrs[p]
  #print r'%s -> node%d [style=dashed];' % (ptrname(p), n)

print "}"
