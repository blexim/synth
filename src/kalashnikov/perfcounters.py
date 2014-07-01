#!/usr/bin/python

import time
import args
import cPickle

args.argparser.add_argument("--stats", default=None, type=str,
    help="file to serialize statistics to")
args.argparser.add_argument("--paramils", default=False, type=bool)

counters = {}
timers = {}

def inc(key):
  if key in counters:
    counters[key] += 1
  else:
    counters[key] = 1

def add(key, v):
  if key in counters:
    counters[k] += v
  else:
    counter[key] = v

def set(key, v):
  counters[key] = v

def start(key="_"):
  global timers

  if key == "_":
    counter = {}
    timers = {}

  if key not in timers:
    timers[key] = []

  timers[key].append((time.time(), None))

def end(key="_"):
  (start, x) = timers[key][-1]
  timers[key][-1] = (start, time.time())

def summary():
  try:
    if args.args.stats is not None:
      f = open(args.args.stats, 'wb')
      stats = (counters, timers)
      cPickle.dump(stats, f, protocol=-1)
      f.close()
  except:
    pass

  print "Perf counters:"
  print counters

  print "Perf timers:"

  runtime = 0

  for (key, times) in timers.iteritems():
    total = sum(end - start for (start, end) in times if end is not None)
    total += sum(time.time() - start for (start, end) in times if end is None)
    print "%s: %.02fs" % (key, total)

    if key == "_":
      runtime = total

  if "timeout" in counters:
    res = "TIMEOUT"
  else:
    res = "SAT"

  if args.args.paramils:
    print "Result for ParamILS: %s, %f, %d, 0, %d" % (
       res, runtime, counters['iterations'], args.args.seed)
