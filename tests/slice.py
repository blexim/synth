#!/usr/bin/python

import re
import sys

line1re = re.compile('t(\d+) = .*?((a|t)\d+)$')
line2re = re.compile('t(\d+) = .*((a|t)\d+).*((a|t)\d+)$')
retre = re.compile('return t(\d+)')

prog = []
ret = -1
lhs = -1

f = open(sys.argv[1])

for l in f:
  l = l.strip('\n')
  m1 = line1re.match(l)
  m2 = line2re.match(l)
  m3 = retre.match(l)

  if m2:
    lhs = int(m2.group(1))
    rhs = [m2.group(2), m2.group(4)]
    prog.append((rhs, m1.string))
  elif m1:
    lhs = int(m1.group(1))
    rhs = [m1.group(2)]
    prog.append((rhs, m1.string))
  elif m3:
    ret = int(m3.group(1))

  if lhs == 0:
    prog = [prog[-1]]

f.close()

live = set([ret])

for i in xrange(len(prog), 0, -1):
  j = i-1

  if j in live:
    l = prog[j][0]

    for v in l:
      if v[0] == 't':
        idx = int(v[1:])
        live.add(idx)

for i in xrange(len(prog)):
  if i in live:
    print prog[i][1]

print 'return t%d' % ret
