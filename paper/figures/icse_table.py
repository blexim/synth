#!/usr/bin/python

import matplotlib.pyplot as plt
import re

benchmark_dir = "../../benchmarks"

# each data point is (runtime (s), runtime semibiased standard, runtime semibiased ext., std = ext., #lines)
brahma = [
    (1.48, 0.8, 0.8, True, 2),
    (7.35, 4.75, 4.75, True, 2),
    (1.6, 0.65, 0.65, True, 2),
    (1.65, 0.86, 0.86, True, 2),
    (3.92, 2.28, 2.28, True, 2),
    (6.22, 1.64, 1.64, True, 2),
    (1.39, .5, .5, True, 3),
    (2.2, 1.42, 1.42, True, 3),
    (4.95, 3.85, 4.9, False, 3),
    (13.99, 4.57, 3.25, False, 3),
    (24.31, 2.86, 14.27, False, 3),
    (279.49, 2.64, 45.52, False, 3),
    (32.5, 3.02, 6.95, False, 4),
    (14.32, 3, 3.66, False, 4),
    (167.84, 4.5, 13.57, False, 4),
    (66.93, 4.95, 18.97, False, 4),
    (228.78, 7.98, 25.55, False, 4),
    (163.82, 65.45, 65.45, True, 4),
    (214.14, 19.3, 63.23, False, 6),
    (1074.04, 13.28, 272.28, False, 7),
    (3600, 187.17, 185.57, False, 12)
]

mappings = [
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
    (25, 30)
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

def make_graph():
  kalashnikov = [load_file("%s/%d.out" % (benchmark_dir, i))
      for i in xrange(1, len(brahma) + 1)]

  print "\\begin{tabular}{l||rrr|rrr}"
  print "Problem & \multicolumn{3}{c}{\\sc Brahma} & \multicolumn{3}{|c}{\\sc Kalashnikov} \\\\"
  print "        & Iter. & Runtime & \#Lines & Iter. & Runtime & \#Lines \\\\"

  print "\\hline"
  print "\\hline"

  for i in xrange(len(brahma)):
    (brit, brt, brinsts) = brahma[i]
    (kalcnt, kaltimes) = kalashnikov[i]

    mintime = min(brt, kaltimes['_'])
    maxinsts = max(brinsts, kalcnt['insts'])

    line = "p%d & " % (i+1)


    def f(t, its, insts):
      ret = '%d & ' % its

      if t == mintime:
        ret += "{\\bf %.02fs} &" % t
      elif t == 3600.0:
        ret  += "-- &"
      else:
        ret += "%.02fs &" % t

      if t == 3600.0:
        ret += '-- &'
      elif insts < maxinsts:
        ret += '{\\bf %d} &' % insts
      else:
        ret += '%d &' % insts

      return ret

    line += f(brt, brit, brinsts)
    line += f(kaltimes['_'], kalcnt['iterations'], kalcnt['insts'])

    line = line[:-1]

    print "%s\\\\" % line

  print "\\end{tabular}"

if __name__ == '__main__':
  make_graph()
