#include <stdio.h>
#include <assert.h>

#ifndef NNODES
 #define NNODES 5
#endif

#define NMATRIX (NNODES + NPROG)

#ifndef NPROG
 #define NPROG NNODES
#endif

#define ABSSIZE (NPROG*NPROG*3 + NPROG*2)

#define INF 0xffffffff

#define idx(x, y) (x*NNODES + y)
#define ptr(x) (NNODES + x)

#define abs_idx(x, y) (x*NPROG + y)
#define cut_idx(x, y) (NPROG*NPROG + NPROG*x + y)
#define cut_cut_idx(x, y) (NPROG*NPROG*2 + NPROG*x + y)
#define cycle_idx(x) (NPROG*NPROG*3 + x)
#define cycle_dist_idx(x) (NPROG*NPROG*3 + NPROG + x)

#define min(x, y) (x < y ? x : y)

typedef unsigned int concrete_heapt[NMATRIX];
typedef unsigned int abstract_heapt[ABSSIZE];

void abstract(concrete_heapt concrete,
              abstract_heapt abstraction);

int is_valid_heap(concrete_heapt heap);

int succ(concrete_heapt heap, unsigned int x);

int heaps_isomorphic(concrete_heapt heap1,
                     concrete_heapt heap2);

int abstractions_equal(abstract_heapt heap1,
                       abstract_heapt heap2);

void concrete_assign(unsigned int x,
                     unsigned int y,
                     concrete_heapt pre,
                     concrete_heapt post);
void abstract_assign(unsigned int x,
                     unsigned int y,
                     abstract_heapt pre,
                     abstract_heapt post);
