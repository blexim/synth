#include <stdio.h>
#include <assert.h>

#if 1
 #define WIDTH 3
 typedef unsigned __CPROVER_bitvector[WIDTH] word_t;
 #define INF ((word_t) -1)
#else
 typedef unsigned int word_t;
 #define INF 0xffffffff
#endif

#ifndef NNODES
 #define NNODES 5
#endif

#define NMATRIX (NNODES + NPROG)

#ifndef NPROG
 #define NPROG NNODES
#endif

#define ABSSIZE (NPROG*NPROG*3 + NPROG*2)

#define idx(x, y) (x*NNODES + y)
#define ptr(x) (NNODES + x)

#define abs_idx(x, y) (x*NPROG + y)
#define cut_idx(x, y) (NPROG*NPROG + NPROG*x + y)
#define cut_cut_idx(x, y) (NPROG*NPROG*2 + NPROG*x + y)
#define cycle_idx(x) (NPROG*NPROG*3 + x)
#define cycle_dist_idx(x) (NPROG*NPROG*3 + NPROG + x)

#define min(x, y) (x < y ? x : y)

typedef struct concrete_heap {
  word_t succ[NNODES];
  word_t ptr[NPROG];
} concrete_heapt;

typedef struct abstract_heap {
  word_t dist[NPROG][NPROG];
  word_t cut[NPROG][NPROG];
  word_t cut_cut[NPROG][NPROG];
  word_t stem[NPROG];
  word_t cycle[NPROG];
} abstract_heapt;

void abstract(concrete_heapt *concrete,
              abstract_heapt *abstraction);

int is_valid_heap(concrete_heapt *heap);

int succ(concrete_heapt *heap, word_t x);

int heaps_isomorphic(concrete_heapt *heap1,
                     concrete_heapt *heap2);

int abstractions_equal(abstract_heapt *heap1,
                       abstract_heapt *heap2);

void concrete_assign(word_t x,
                     word_t y,
                     concrete_heapt *pre,
                     concrete_heapt *post);
void abstract_assign(word_t x,
                     word_t y,
                     abstract_heapt *pre,
                     abstract_heapt *post);
