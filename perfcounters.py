#!/usr/bin/python

import time
import args

counters = {}
timers = {}

def inc(key):
  if key in counters:
    counters[key] += 1
  else:
    counters[key] = 1

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
  print "Perf counters:"
  print counters

  print "Perf timers:"

  for (key, times) in timers.iteritems():
    total = sum(end - start for (start, end) in times)
    print "%s: %.02fs" % (key, total)

