#!/usr/bin/python

import scatter
import stats
import sys

(name1, bench1) = stats.load(sys.argv[1])
(name2, bench2) = stats.load(sys.argv[2])

aggregate = stats.compare(bench1, bench2)
stats.print_stats(name1, name2, aggregate)

times = scatter.load(sys.argv[1], sys.argv[2])
scatter.plot(name1, name2, times).show()
