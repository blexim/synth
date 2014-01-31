#!/usr/bin/python

import re
import os
import cPickle
import slice_log

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

  r = re.compile('t(\d+) =')
  lines = f.readlines()

  for l in lines:
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

  sliced_prog = slice_log.slice(lines)
  counters['insts'] = len(sliced_prog) - 1

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
  import sys

  results = process_dir(sys.argv[1])
  processed_f = os.path.basename(sys.argv[1]) + '.stats'
  processed = os.path.join(processed_dir, processed_f)

  print processed

  f = open(processed, 'wb')
  cPickle.dump(results, f)
  f.close()
