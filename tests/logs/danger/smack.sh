#!/bin/sh

benchmark=`basename $1`
smack=/mnt/disk2/src/smack/bin/smackverify.py
(time $smack --loop-limit 1000005 --time-limit 180 $1 > $benchmark.smack.log) 2> $benchmark.smack.log
