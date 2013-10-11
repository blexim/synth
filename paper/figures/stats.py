#!/usr/bin/python

import re

benchmark_dir = "../../benchmarks"

# each data point is (#iterations, runtime (s), #lines)
brahma = [
  (2, 3.2, 2),
  (3, 3.6, 2),
  (3, 1.4, 2),
  (2, 3.3, 2),
  (3, 2.2, 2),
  (2, 2.4, 2),
  (2, 1.0, 3),
  (2, 1.4, 3),
  (2, 5.8, 3),
  (14, 76.1, 3),
  (7, 57.1, 3),
  (9, 67.8, 3),
  (4, 6.2, 4),
  (4, 59.6, 4),
  (8, 118.9, 4),
  (5, 62.3, 4),
  (6, 78.1, 4),
  (5, 45.9, 6),
  (5, 34.7, 6),
  (6, 108.4, 7),
  (5, 28.3, 8),
  (8, 279.0, 8),
  (8, 1668.0, 10),
  (9, 224.9, 12),
  (11, 2778.7, 16)
]

def load_file(filename):
  counters = {}
  timers = {}

  try:
    f = open(filename)
  except:
    return ({"timeout": "1", 'insts': 0}, {'_': 3600.0})

  START = 0
  COUNTERS = 1
  TIMERS = 2

  state = START
  insts = 0

  r = re.compile('t(\d+) =')

  for l in f.readlines():
    l = l.strip()

    if state == START and l == "Perf counters:":
      state = COUNTERS
      continue
    elif state == COUNTERS and l == "Perf timers:":
      state = TIMERS
      continue

    m = r.match(l)

    if m:
      insts = int(m.group(1))

    if state == COUNTERS:
      counters = eval(l)
    elif state == TIMERS:

      if ':' not in l:
        k = '_'
        val = l
      else:
        (k, val) = l.split(':')

      # Strip the trailing 's' from val...
      val = val[:-1]

      timers[k] = float(val)

  counters['insts'] = insts

  if 'timeout' in counters or '_' not in timers:
    timers['_'] = 3600.0

  if 'iterations' not in counters:
    counters['iterations'] = 0

  return (counters, timers)

def mean(l):
  return sum(l) / len(l)

def med(l):
  return sorted(l)[len(l)/2]

def make_graph():
  kalashnikov = [load_file("%s/%d.out" % (benchmark_dir, i))
      for i in xrange(1, len(brahma) + 1)]
  cnt = 0
  ktotal = 0
  btotal = 0
  kfaster = 0
  absspeedups = []
  relspeedups = []

  for i in xrange(len(brahma)):
    (brit, brt, brinsts) = brahma[i]
    (kalcnt, kaltimes) = kalashnikov[i]

    if 'timeout' not in kalcnt and brinsts == kalcnt['insts']:
      cnt += 1

      kt = kaltimes['_']

      ktotal += kt
      btotal += brt

      if kt < brt:
        kfaster += 1

      absspeedups.append(brt - kt)
      relspeedups.append(brt / kt)



  print "Both solved:"
  print "Kalashnikov faster: %d/%d times" % (kfaster, cnt)
  print "Kalashnikov total: %.02fs" % ktotal
  print "Brahma total: %.02fs" % btotal
  print "Mean/median absolute speedup: %.02fs/%.02fs" % (mean(absspeedups), med(absspeedups))
  print "Mean/median relative speedup: %.02f/%.02f" % (mean(relspeedups), med(relspeedups))

if __name__ == '__main__':
  make_graph()
