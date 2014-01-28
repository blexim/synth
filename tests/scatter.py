#!/usr/bin/python

import matplotlib.pyplot as plt
import cPickle

timeout = 3600

def load(fname1, fname2):
  f1 = open(fname1, 'rb')
  stats1 = cPickle.load(f1)
  f1.close()

  f2 = open(fname2, 'rb')
  stats2 = cPickle.load(f2)
  f2.close()

  common_keys = [k for k in stats1 if k in stats2]

  ret1 = []
  ret2 = []

  for k in common_keys:
    time1 = stats1[k][1]['_']
    time2 = stats2[k][1]['_']

    if time1 < 0:
      time1 = timeout

    if time2 < 0:
      time2 = timeout

    ret1.append(time1)
    ret2.append(time2)

  return (ret1, ret2)

def plot(name1, name2, times):
  plt.title("%s vs. %s" % (name1, name2))

  ax = plt.subplot(1, 2, 1)
  plt.xlim(0, timeout)
  plt.ylim(0, timeout)
  plt.xscale('log')
  plt.yscale('log')
  plt.xlabel("%s runtime (s)" % name1)
  plt.ylabel("%s runtime (s)" % name2)
  plt.plot(times[0], times[1], 'ro')

  ax2 = plt.subplot(1, 2, 2)
  plt.xscale('linear')
  plt.yscale('linear')
  plt.xlim(0, 1)
  plt.ylim(0, 1)
  plt.plot([0, 1], [0, 1], 'k-')

  ax.set_position([0.1, 0.1, 0.8, 0.8])
  ax2.set_position([0.1, 0.1, 0.8, 0.8])

  ax2.set_axis_off()

  plt.axhline(color='k')
  plt.axvline(color='k')
  plt.axhline(y=1, color='k')
  plt.axvline(x=1, color='k')

  return plt

if __name__ == '__main__':
  import sys

  fname1 = sys.argv[1]
  expname1 = sys.argv[2]

  fname2 = sys.argv[3]
  expname2 = sys.argv[4]

  times = load(fname1, fname2)
  graph = plot(expname1, expname2, times)
  graph.show()
