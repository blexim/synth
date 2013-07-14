#!/usr/bin/python

import time

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

def summary(args):
  pass
