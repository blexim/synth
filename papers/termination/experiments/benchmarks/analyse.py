#!/usr/bin/python

import cPickle
import re
import os

propre = re.compile(r'([a-zA-Z_-]+): *(.*)')
logdir = "logs"

def load_stats(filename):
  try:
    f = open(filename)
    stats = cPickle.load(f)
    f.close()
  except:
    return None

  return stats

def load_props(filename):
  props = {}

  f = open(filename)

  REST = 0
  COMMENT = 1
  state = REST
  loc = 0

  for l in f:
    l = l.strip()

    if state == REST:
      if '/*' in l:
        state = COMMENT
      else:
        if l != '':
          loc += 1
    elif state == COMMENT:
      if '*/' in l:
        state = REST
      elif ':' in l:
        m = propre.search(l)

        if m:
          key = m.group(1).lower()
          val = m.group(2).lower()
          props[key] = val

  f.close()

  props['loc'] = str(loc)
  return props

def load_benchmark(cfile):
  global logdir

  props = load_props(cfile)
  benchname = os.path.basename(cfile)
  #benchname = os.path.basename(cfile).partition('.')[0]

  termfile = os.path.join(logdir, '%s.term.stats' % benchname)
  nontermfile = os.path.join(logdir, '%s.nonterm.stats' % benchname)

  termstats = load_stats(termfile)
  nontermstats = load_stats(nontermfile)

  return (benchname, props, termstats, nontermstats)

def print_benchmark(benchmark):
  (benchname, props, termstats, nontermstats) = benchmark

  loc = props.get('loc', '')
  linprog = props.get('linear-program', '')
  linrank = props.get('linear-rank', '')
  iscond = props.get('conditional', '')
  isfloat = props.get('float', '')
  lexdim = props.get('lexicographic', '')
  isterm = props.get('terminates', '')

  res = '?'
  elapsed = 'T/O'
  iters = '0'

  if termstats: 
    (counters, timers) = termstats
    iters = str(counters['iterations'])

    if 'timeout' not in counters:
      (start, end) = timers['_'][0]
      elapsed = '%.01fs' % (end - start)
      res = 'term'
    elif nontermstats:
      (counters, timers) = nontermstats
      iters = str(counters['iterations'])

      if 'timeout' not in counters:
        (start, end) = timers['_'][0]
        elapsed = '%.01fs' % (end - start)
        res = 'nonterm'
  else:
    return ""
    res = 'err'
    elapsed = '--'

  return ' & '.join((benchname, loc, isterm, linprog, linrank, iscond,
                     isfloat, lexdim, '5', res, elapsed, iters)) + '\\\\ \n'

def munge(s):
  REST = 0
  INT = 1
  state = REST
  ret = []
  acc = 0

  for c in s:
    if c.isdigit():
      if state == INT:
        acc *= 10
        acc += int(c)
      else:
        state = INT
        acc = int(c)
    else:
      if state == INT:
        ret.append(acc)
        ret.append(c)
        state = REST
      else:
        ret.append(c)

  if state == INT:
    ret.append(acc)

  return ret

def print_all(dir):
  fs = [(munge(s), s) for s in os.listdir(dir)]

  for (_, f) in sorted(fs) :
    if f.endswith('.c') and (f.startswith('svcomp') or f.startswith('loop')):
      benchmark = load_benchmark(os.path.join(dir, f))
      print print_benchmark(benchmark)

if __name__ == '__main__':
  print_all('.')
