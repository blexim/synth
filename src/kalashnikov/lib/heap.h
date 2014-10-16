#ifndef HEAP_H
#define HEAP_H

#include <stdio.h>
#include <assert.h>

#include "synth.h"

#define INF WORDMASK

#ifdef SEARCH
 #define __CPROVER_assume(x)
#endif

#ifndef NHEAP
 #define NHEAP 0
#endif

typedef word_t ptr_t;
typedef word_t node_t;

#define null_ptr (ptr_t) 0
#define null_node (node_t) 0

#ifndef NSLACK
 #define NSLACK 0
#endif

#ifndef NLIVE
 #define NLIVE (NHEAP-1)
#endif

#define NABSNODES ((NLIVE*2) + 1 + NSLACK)

typedef struct abstract_heap {
  // A map from nodes to nodes saying for each node n what its successor is.
  node_t succ[NABSNODES];

  // A map from nodes to distances, saying for each node n how far away its
  // successor is.
  word_t dist[NABSNODES];

  // A map from pointers to nodes, saying for each pointer which node it points
  // to.
  node_t ptr[NHEAP];

  // How many nodes are currently allocated?
  word_t nnodes;
} abstract_heapt;

word_t path_len(abstract_heapt *heap,
                ptr_t x,
                ptr_t y);
word_t alias(abstract_heapt *heap,
             ptr_t x,
             ptr_t y);
word_t is_null(abstract_heapt *heap,
               ptr_t x);

#define is_path(h, x, y) (path_len(h, x, y) != INF)
#define circular(h, x) (!is_path(h, x, null_ptr))

void print_abstract(abstract_heapt *abstract);

void abstract_assign(abstract_heapt *pre,
                     abstract_heapt *post,
                     ptr_t x,
                     ptr_t y);
void abstract_lookup(abstract_heapt *pre,
                     abstract_heapt *post,
                     ptr_t x,
                     ptr_t y);
void abstract_update(abstract_heapt *pre,
                     abstract_heapt *post,
                     ptr_t x,
                     ptr_t y);
void abstract_new(abstract_heapt *pre,
                  abstract_heapt *post,
                  ptr_t x);

int valid_abstract_heap(abstract_heapt *heap);
int is_minimal(abstract_heapt *heap);

word_t s_add(word_t x, word_t y);
word_t s_sub(word_t x, word_t y);

#endif // HEAP_H
