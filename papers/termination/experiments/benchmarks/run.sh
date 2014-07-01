#!/bin/bash

d=`pwd`
logdir=$d/logs
mkdir $logdir

cd ../../../../src/kalashnikov

for b in $d/svcomp*.c $d/loop*.c
do
  b=`basename $b`
  logfile=$logdir/$b.term.log

  echo $b termination
  ./frontend.py $d/$b -v -T 60 --stats $logdir/$b.term.stats > $logfile

  if grep -q Timeout $logfile;
  then
    echo $b nontermination
    ./nonterm.py $d/$b -v -T 60 --stats $logdir/$b.nonterm.stats > $logdir/$b.nonterm.log
  fi
done
