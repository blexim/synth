#!/usr/bin/python

import cPickle
import re
import os

propre = re.compile(r'([a-zA-Z_-]+): *(.*)')
logdir = "logs"

TERM = "\\tick"
NONTERM = "\\xmark"
UNK = "?"
TO = "--"

def load_stats(filename):
  try:
    f = open(filename)
    stats = cPickle.load(f)
    f.close()
  except:
    return None

  return stats

def load_armc(filename):
  ret = {}

  f = open(filename)

  for l in f:
    if 'SPINS' in l:
      ret['res'] = NONTERM
    elif 'TERMINATES' in l:
      ret['res'] = TERM
    elif 'TIMEOUT' in l:
      ret['res'] = TO
      ret['elapsed'] = 'T/O'
    elif 'UNK' in l:
      ret['res'] = UNK
    else:
      ret['elapsed'] = l.strip() + "s"

  f.close()
  return ret
      

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
          val = m.group(2)
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
  armcfile = os.path.join(logdir, '%s.armc.res' % benchname)

  termstats = load_stats(termfile)
  nontermstats = load_stats(nontermfile)
  armc = load_armc(armcfile)

  return (benchname, props, termstats, nontermstats, armc)

armc_correct = 0
armc_incorrect = 0
armc_unk = 0
armc_to = 0

headshot_correct = 0
headshot_incorrect = 0
headshot_unk = 0
headshot_to = 0

def print_benchmark(benchmark):
  global armc_correct, armc_incorrect, armc_unk, armc_to
  global headshot_correct, headshot_incorrect, headshot_unk, headshot_to

  (benchname, props, termstats, nontermstats, armc) = benchmark

  loc = props.get('loc', '')
  linprog = props.get('linear-program', '')
  linrank = props.get('linear-rank', '')
  iscond = props.get('conditional', '')
  isfloat = props.get('float', '')
  lexdim = props.get('lexicographic', '')
  isterm = props.get('terminates', '')
  tweaked = props.get('tweaked', '').lower() == 'true'

  if 'bibtex' in props:
    benchname += '~\cite{%s}' % props['bibtex']

  if isterm.lower() == 'true':
    isterm = TERM
  elif isterm.lower() == 'false':
    isterm = NONTERM
  else:
    isterm = UNK

  res = TO
  elapsed = 'T/O'
  iters = '0'

  if termstats: 
    (counters, timers) = termstats
    iters = str(counters['iterations'])

    if 'timeout' not in counters:
      (start, end) = timers['_'][0]
      elapsed = '%.01fs' % (end - start)
      res = TERM
    elif nontermstats:
      (counters, timers) = nontermstats
      iters = str(counters['iterations'])

      if 'timeout' not in counters:
        (start, end) = timers['_'][0]
        elapsed = '%.01fs' % (end - start)
        res = NONTERM

    if tweaked:
      elapsed += '*'
  else:
    return ""
    res = 'err'
    elapsed = '--'

  armcres = armc['res']
  armctime = armc['elapsed']

  if res not in (UNK, TO) and isterm != UNK:
    if res == isterm:
      headshot_correct += 1
    else:
      headshot_incorrect += 1
  elif res == UNK:
    headshot_unk += 1
  elif res == TO:
    headshot_to += 1

  if armcres not in (UNK, TO) and isterm != UNK:
    if armcres == isterm:
      armc_correct += 1
    else:
      armc_incorrect += 1
  elif armcres == UNK:
    armc_unk += 1
  elif armcres == TO:
      armc_to += 1

  return ' & '.join((benchname, isterm, armcres, armctime, res, elapsed, iters)) + '\\\\ \n'

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

  print r"\hline  "
  print r"\hline "
  print (r"\multicolumn{2}{|l||}{Correct} & \multicolumn{2}{|r||}{%d} & \multicolumn{3}{|r|}{%d} \\" %
      (armc_correct, headshot_correct))

  print (r"\multicolumn{2}{|l||}{Incorrect for bit-vectors} & \multicolumn{2}{|r||}{%d} & \multicolumn{3}{|r|}{%d} \\" %
      (armc_incorrect, headshot_incorrect))

  print (r"\multicolumn{2}{|l||}{Unknown} & \multicolumn{2}{|r||}{%d} & \multicolumn{3}{|r|}{%d} \\" %
      (armc_unk, headshot_unk))

  print (r"\multicolumn{2}{|l||}{Timeout} & \multicolumn{2}{|r||}{%d} & \multicolumn{3}{|r|}{%d} \\" %
      (armc_to, headshot_to))



if __name__ == '__main__':
  print_all('.')
