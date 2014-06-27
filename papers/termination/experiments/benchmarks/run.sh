#!/bin/sh

d=`pwd`
logdir=$d/logs
mkdir $logdir

cd ../../../../src/kalashnikov

for b in svcomp1 svcomp2 svcomp3 svcomp4 svcomp5 svcomp7 svcomp8 svcomp9 svcomp10 svcomp11 svcomp13 svcomp14 svcomp15 svcomp16 svcomp17 svcomp25 svcomp26 svcomp27 svcomp28 svcomp29 svcomp37 svcomp38 svcomp39 svcomp42
do
  logfile=$logdir/$b.term.log

  echo $b termination
  ./frontend.py $d/$b.c -v -T 120 -s5 -c1 --strategy=evolve --stats $logdir/$b.term.stats > $logfile

  if grep -q Timeout $logfile;
  then
    echo $b nontermination
    ./nonterm.py $d/$b.c -v -T 120 -s5  -c1 --strategy=evolve --stats $logdir/$b.nonterm.stats > $logdir/$b.nonterm.log
  fi
done
