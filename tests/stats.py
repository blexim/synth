#!/usr/bin/python

import cPickle
import scipy.stats
import os

threshold = 0.05

def load(filename):
  f = open(filename, 'rb')
  benchmarks = cPickle.load(f)
  f.close()

  name = os.path.basename(filename)
  name = name[:name.index('.')]

  return (name, benchmarks)

def median(l):
  return sorted(l)[len(l) / 2]

def compare(bench1, bench2):
  both_solved = [(bench1[k][1]['_'], bench2[k][1]['_'])
      for k in bench1
      if k in bench2 and
      bench1[k][1]['_'] >= 0 and bench2[k][1]['_'] >= 0]
  solved1 = [x for (x, y) in both_solved]
  solved2 = [y for (x, y) in both_solved]
  speedups = [y - x for (x, y) in both_solved]

  only1 = [k for k in bench1
      if (bench1[k][1]['_'] >= 0) and
         (k not in bench2 or bench2[k][1]['_'] < 0)]
  only2 = [k for k in bench2
      if (bench2[k][1]['_'] >= 0) and
         (k not in bench1 or bench1[k][1]['_'] < 0)]


  total1 = sum(solved1)
  total2 = sum(solved2)

  med1 = median(solved1)
  med2 = median(solved2)

  medspeedup = median(speedups)

  (uval, pval) = scipy.stats.wilcoxon(solved1, solved2)

  return (total1, total2, med1, med2, medspeedup, len(only1), len(only2),
      pval, uval, len(both_solved))

def print_stats(n1, n2, stats):
  (total1, total2, med1, med2, medspeedup, only1, only2, pval, uval, cnt) = stats
  totalspeedup = total2 - total1

  maxlen = max(len(n1), len(n2))
  m1 = '%s%s' % (n1, ' ' * (maxlen-len(n1)))
  m2 = '%s%s' % (n2, ' ' * (maxlen-len(n2)))

  print ""
  print " %s | Total time | Median time | Uniquely solved" % (" " * maxlen)
  print "-%s----------------------------------------------" % ("-" * maxlen)
  print " %s | %9.2fs | %10.2fs | %15d" % (m1, total1, med1, only1)
  print " %s | %9.2fs | %10.2fs | %15d" % (m2, total2, med2, only2)
  print " diff%s | %9.2fs | %10.2fs |" % (' ' * (maxlen-4),
      totalspeedup, medspeedup)
  print ""
  print "Both solved %d cases" % cnt
  print ""

  if pval <= threshold:
    if med1 < med2:
      print ("%s is SIGNIFICANTLY faster " % n1),
    else:
      print ("%s is SIGNIFICANTLY faster " % n2),
  else:
    print "No signficant speed difference ",

  print "(p=%.3f, U=%.3f)" % (pval, uval)

if __name__ == '__main__':
  import sys

  (n1, bench1) = load(sys.argv[1])
  (n2, bench2) = load(sys.argv[2])

  stats = compare(bench1, bench2)

  print_stats(n1, n2, stats)
