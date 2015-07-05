#!/bin/bash

ESOLVER=/mnt/disk2/src/sygus-comp14/solvers/enumerative/esolver-synth-lib/bin/opt/esolver-synthlib

benchmark=`basename $1`
(time ${ESOLVER} -t 180 -v 1 $1 > ${benchmark}.log) 2> $benchmark.log
