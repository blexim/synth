#!/usr/bin/python

import matplotlib.pyplot as plt

benchmark_dir = "../../benchmarks"

# each data point is (#iterations, runtime (s))
brahma = [
  (2, 3.2),
  (3, 3.6),
  (3, 1.4),
  (2, 3.3),
  (3, 2.2),
  (2, 2.4),
  (2, 1.0),
  (2, 1.4),
  (2, 5.8),
  (14, 76.1),
  (7, 57.1),
  (9, 67.8),
  (4, 59.6),
  (8, 118.9),
  (5, 62.3),
  (6, 78.1),
  (5, 45.9),
  (5, 34.7),
  (6, 108.4),
  (5, 28.3),
  (8, 279.0),
  (8, 1668.0),
  (9, 224.9),
  (11, 2778.7)
]

def load_file(filename):
  f = open(filename)
  counters = {}
  timers = {}

  START = 0
  COUNTERS = 1
  TIMERS = 2

  state = START

  for l in f.readlines():
    l = l.strip()

    if state == START and l == "Perf counters:":
      state = COUNTERS
      continue
    elif state == COUNTERS and l == "Perf timers:":
      state = TIMERS
      continue

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

  return (counters, timers)

def file_to_time(filename):
  (counters, timers) = load_file(filename)

  if "timeout" in counters or "_" not in timers:
    return 3600
  else:
    return timers["_"]

def make_graph():
  brahma_times = [t for (its, t) in brahma]
  kalashnikov_times = [file_to_time("%s/%d.out" % (benchmark_dir, i))
      for i in xrange(1, len(brahma_times) + 1)]
  kalashnikov_no_width_times = [file_to_time("%s/nowidth/%d.out" % (benchmark_dir, i))
      for i in xrange(1, len(brahma_times) + 1)]
  kalashnikov_cbmc_times = [file_to_time("%s/cbmc_%d.out" % (benchmark_dir, i))
      for i in xrange(1, len(brahma_times) + 1)]

  print "\\begin{tabular}{l|l|l|l|l}"
  print "Problem & {\\sc Brahma} & {\\sc Kalashnikov} & {\\sc Kalashnikov} & {\\sc Kalashnikov} \\\\"
  print "        &               &                    & (no width)         & (CBMC only) \\\\"

  print "\\hline"

  for i in xrange(len(brahma_times)):
    times = (brahma_times[i], kalashnikov_times[i], kalashnikov_no_width_times[i],
        kalashnikov_no_width_times[i])
    mintime = min(times)

    line = "p%d & " % (i+1)

    for t in times:
      if t == mintime:
        line += "{\\bf %.02fs} &" % t
      elif t == 3600.0:
        line += "- &"
      else:
        line += "%.02fs &" % t

    line = line[:-1]

    print "%s\\\\" % line

  print "\\end{tabular}"

if __name__ == '__main__':
  make_graph()
