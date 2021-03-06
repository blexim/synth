#!/usr/bin/python

import re

benchmark_dir = "../../benchmarks"

# each data point is (runtime (s), runtime semibiased standard, runtime semibiased ext., std = ext., #lines)
brahma = [
    (1.48, 0.8, 0.8, True, 2),   #1
    (7.35, 4.75, 4.75, True, 2), #2
    (1.6, 0.65, 0.65, True, 2), #3
    (1.65, 0.86, 0.86, True, 2), #4
    (3.92, 2.28, 2.28, True, 2), #5
    (6.22, 1.64, 1.64, True, 2), #6
    (1.39, .5, .5, True, 3),     #7
    (2.2, 1.42, 1.42, True, 3),  #8
    (4.95, 3.85, 4.9, False, 3), #9
    (13.99, 4.57, 3.25, False, 3), #10
    (24.31, 2.86, 14.27, False, 3), #11
    (279.49, 2.64, 45.52, False, 3), #12
    (32.5, 3.02, 6.95, False, 4), #13
    (14.32, 3, 3.66, False, 4),   #14
    (167.84, 4.5, 13.57, False, 4), #15
    (66.93, 4.95, 18.97, False, 4), #16
    (217.34, 5.89, 20.62, False, 4), #17
    (228.78, 7.98, 25.55, False, 4), #18
    (163.82, 65.45, 65.45, True, 4), #19
    (214.14, 19.3, 63.23, False, 6), #22
    (1074.04, 13.28, 272.28, False, 7), #21
    (3600, 187.17, 185.57, False, 12),  #22
    (1.38, 12.12, 12.12, True, 3),   #23
    (5.28, 2.96, 2.96, True, 4)  #24
]

mappings = dict([
    (1, 1),
    (2, 2),
    (3, 3),
    (4, 4),
    (5, 5),
    (6, 6),
    (7, 7),
    (8, 8),
    (9, 9),
    (10, 10),
    (11, 11),
    (12, 12),
    (13, 13),
    (14, 26),
    (15, 14),
    (16, 16),
    (17, 27),
    (18, 15),
    (19, 17),
    (20, 18),
    (21, 20),
    (22, 24),
    (23, 28),
    (24, 29),
    #(25, 30)
])

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
  return sum(l)/len(l)

def med(l):
  return sorted(l)[len(l)/2]

def make_graph():
  kalashnikov = [load_file("%s/%d.out" % (benchmark_dir, mappings[i]))
      for i in xrange(1, len(brahma) + 1)]
  cnt = 0
  ktotal = 0
  btotal = 0
  kfaster = 0
  absspeedups = []
  relspeedups = []

  for i in xrange(len(brahma)):
    (brt, brstt, brext, breq, brl) = brahma[i]
    (kalcnt, kaltimes) = kalashnikov[i]

    if breq:
      brt = brstt
    else:
      brt = brstt + brext

    if 'timeout' not in kalcnt and brl == kalcnt['insts'] and breq:
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
