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
      (k, val) = l.split(':')

      # Strip the trailing 's' from val...
      val = val[:-1]

      timers[k] = float(val)

  return (counters, timers)

def make_graph():
  brahma_times = [t for (its, t) in brahma]
  kalashnikov_times = []

  for i in xrange(1, len(brahma_times) + 1):
    filename = "%s/%d.out" % (benchmark_dir, i)
    (counters, timers) = load_file(filename)

    if "timeout" in counters:
      kalashnikov_times.append(3600)
    else:
      kalashnikov_times.append(timers["_"])

  plt.title("Brahma vs. Kalashnikov")

  ax = plt.subplot(1, 2, 1)
  plt.xlim(0, 3600)
  plt.ylim(0, 3600)
  plt.xscale('log')
  plt.yscale('log')
  plt.xlabel("Brahma runtime (s)")
  plt.ylabel("Kalashnikov runtime (s)")
  plt.plot(brahma_times, kalashnikov_times, 'ro')

  ax2 = plt.subplot(1, 2, 2)
  plt.xscale('linear')
  plt.yscale('linear')
  plt.xlim(0, 1)
  plt.ylim(0, 1)
  plt.plot([0, 1], [0, 1], 'k-')

  ax.set_position([0.1, 0.1, 0.8, 0.8])
  ax2.set_position([0.1, 0.1, 0.8, 0.8])

  ax2.set_axis_off()

  #plt.show()

  plt.axhline(color='k')
  plt.axvline(color='k')
  plt.axhline(y=1, color='k')
  plt.axvline(x=1, color='k')

  plt.savefig('brahma_kalashnikov.pdf')

if __name__ == '__main__':
  make_graph()
