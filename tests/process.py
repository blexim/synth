#!/usr/bin/python

import re
import os
import cPickle

benchmark_dir = "logs"
processed_dir = "processed"

def load_file(filename):
  counters = {}
  timers = {}

  try:
    f = open(filename)
  except:
    return ({"timeout": "1", 'insts': 0}, {'_': 600.0})

  START = 0
  COUNTERS = 1
  TIMERS = 2

  state = START
  insts = 0
  seen_finished = False

  r = re.compile('.* = .*;')

  for l in f.readlines():
    l = l.strip()

    if "Finished" in l:
      seen_finished = True

    if state == START and l == "Perf counters:":
      state = COUNTERS
      continue
    elif state == COUNTERS and l == "Perf timers:":
      state = TIMERS
      continue

    m = r.match(l)

    if seen_finished and m:
      insts += 1

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
    timers['_'] = -1

  if 'iterations' not in counters:
    counters['iterations'] = 0

  return (counters, timers)

def process_dir(d):
  ret = {}

  for logfile in os.listdir(d):
    absfile = os.path.join(d, logfile)
    (counters, timers) = load_file(absfile)
    testname = logfile[:logfile.rfind('.')]
    ret[testname] = (counters, timers)

  return ret

def process_all_dirs():
  for logdir in os.listdir(benchmark_dir):
    print logdir

    results = process_dir(os.path.join(benchmark_dir, logdir))
    processed = os.path.join(processed_dir, logdir + '.stats')
    f = open(processed, 'wb')
    cPickle.dump(results, f)
    f.close()

if __name__ == '__main__':
  process_all_dirs()
