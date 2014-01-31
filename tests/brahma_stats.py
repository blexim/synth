#!/usr/bin/python

import cPickle

# Each data point is (#iterations, runtime, #lines)
pldi_brahma = [ 
  (2, 3.2, 2), 
  (3, 3.6, 2), 
  (3, 1.4, 2), 
  (2, 3.3, 2), 
  (3, 2.2, 2), 
  (2, 2.4, 2), 
  (2, 1.0, 3), 
  (2, 1.4, 3), 
  (2, 5.8, 3), 
  (14, 76.1, 3), 
  (7, 57.1, 3), 
  (9, 67.8, 3), 
  (4, 6.2, 4), 
  (4, 59.6, 4),
  (8, 118.9, 4),
  (5, 62.3, 4),
  (6, 78.1, 4),
  (5, 45.9, 6),
  (5, 34.7, 6),
  (6, 108.4, 7),
  (5, 28.3, 8),
  (8, 279.0, 8),
  (8, 1668.0, 10),
  (9, 224.9, 12),
  (11, 2778.7, 16)
]

# each data point is (runtime (s), runtime semibiased standard,
#                     runtime semibiased ext., std = ext., #lines)

icse_brahma = [
    (1.48, 0.8, 0.8, True, 2),   #1  
    (7.35, 4.75, 4.75, True, 2), #2
    (1.6, 0.65, 0.65, True, 2), #3
    (1.65, 0.86, 0.86, True, 2), #4
    (3.92, 2.28, 2.28, True, 2), #5
    (6.22, 1.64, 1.64, True, 2), #6
    (1.39, .5, .5, True, 3),     #7  
    (2.2, 1.42, 1.42, True, 3),  #8  
    (4.95, 3.85, 4.9, False, 3), #9
    (13.99, 4.57, 3.25, False, 3), #10 
    (24.31, 2.86, 14.27, False, 3), #11 
    (279.49, 2.64, 45.52, False, 3), #12 
    (32.5, 3.02, 6.95, False, 4), #13 
    (14.32, 3, 3.66, False, 4),   #14 
    (167.84, 4.5, 13.57, False, 4), #15 
    (66.93, 4.95, 18.97, False, 4), #16 
    (217.34, 5.89, 20.62, False, 4), #17 
    (228.78, 7.98, 25.55, False, 4), #18 
    (163.82, 65.45, 65.45, True, 4), #19 
    (214.14, 19.3, 63.23, False, 6), #22 
    (1074.04, 13.28, 272.28, False, 7), #21 
    (-1, 187.17, 185.57, False, 12),  #22 
    (1.38, 12.12, 12.12, False, 3),   #23 
    (5.28, 2.96, 2.96, False, 4)  #24 
]

icse_pldi_map = dict([
    (1, 1), 
    (2, 2), 
    (3, 3), 
    (4, 4), 
    (5, 5), 
    (6, 6), 
    (7, 7), 
    (8, 8), 
    (9, 9), 
    (10, 10),
    (11, 11),
    (12, 12),
    (13, 13),
    (14, 26),
    (15, 14),
    (16, 16),
    (17, 27),
    (18, 15),
    (19, 17),
    (20, 18),
    (21, 20),
    (22, 24),
    (23, 28),
    (24, 29),
    #(25, 30)
])

brahma_stats = {}

for i in xrange(len(pldi_brahma)):
  stats = pldi_brahma[i]
  timers = {'_': stats[1]}
  counters = {'iterations': stats[0], 'insts': stats[2]}

  if i >= 17:
    counters['automatic'] = 0
  else:
    counters['automatic'] = 1

  brahma_stats['%d' % (i+1)] = (counters, timers)

brahmaf = open('processed/brahma.stats', 'wb')
cPickle.dump(brahma_stats, brahmaf, -1)
brahmaf.close()

icse_stats = {}
icse_semibiased_stats = {}

for i in xrange(len(icse_brahma)):
  stats = icse_brahma[i]
  timers = {'_': stats[0]}
  counters = {'insts': stats[4]}

  icse_stats['%d' % icse_pldi_map[i+1]] = (counters, timers)

  if not stats[3]:
    time = stats[1] + stats[2]
    counters['automatic'] = 0
  else:
    counters['automatic'] = 1
    time = stats[1]

  timers = {'_': time}
  icse_semibiased_stats['%d' % icse_pldi_map[i+1]] = (counters, timers)

icsef = open('processed/icse.stats', 'wb')
cPickle.dump(icse_stats, icsef, -1)
icsef.close()

semibiasedf = open('processed/icse_semibiased.stats', 'wb')
cPickle.dump(icse_semibiased_stats, semibiasedf, -1)
semibiasedf.close()
