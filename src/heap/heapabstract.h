#ifndef HEAPABSTRACT_H
#define HEAPABSTRACT_H

#include <stdio.h>
#include <assert.h>

#ifdef VERIF
 #define WIDTH 3
 typedef unsigned __CPROVER_bitvector[WIDTH] word_t;
 #define INF ((word_t) -1)
#else
 typedef unsigned int word_t;
 #define INF 0xffffffff
 #define __CPROVER_assume(x)
#endif

#ifndef NNODES
 #define NNODES 5
#endif

#ifndef NPROG
 #define NPROG NNODES
#endif

#define min(x, y) (x < y ? x : y)

typedef word_t ptr_t;
typedef word_t node_t;

typedef struct concrete_heap {
  node_t succ[NNODES];
  node_t ptr[NPROG];
} concrete_heapt;

#define NABSNODES (NPROG*2 + 1)

typedef struct abstract_heap {
  // A map from nodes to nodes saying for each node n what its successor is.
  node_t succ[NABSNODES];

  // A map from nodes to distances, saying for each node n how far away its
  // successor is.
  word_t dist[NABSNODES];

  // A map from pointers to nodes, saying for each pointer which node it points
  // to.
  node_t ptr[NPROG];

  // How many nodes are currently allocated?
  word_t nnodes;
} abstract_heapt;

typedef struct heap_facts {
  word_t dists[NPROG][NPROG];
} heap_factst;

word_t nil = 0;

void print_concrete(concrete_heapt *heap);
void print_abstract(abstract_heapt *abstract);

void abstract(concrete_heapt *concrete,
              abstract_heapt *abstraction);

int is_valid_heap(concrete_heapt *heap);

int succ(concrete_heapt *heap, word_t x);

int heaps_isomorphic(concrete_heapt *heap1,
                     concrete_heapt *heap2);

void consequences(abstract_heapt *heap,
                  heap_factst *facts);

void gc(abstract_heapt *heap,
        word_t x);

void alias(heap_factst *facts,
           word_t x,
           word_t y);

word_t path(heap_factst *facts,
            word_t x,
            word_t y);

word_t is_path(heap_factst *facts,
               word_t x,
               word_t y);

void concrete_assign(word_t x,
                     word_t y,
                     concrete_heapt *pre,
                     concrete_heapt *post);
void abstract_assign(word_t x,
                     word_t y,
                     abstract_heapt *pre,
                     abstract_heapt *post);

void concrete_lookup(word_t x,
                     word_t y,
                     concrete_heapt *pre,
                     concrete_heapt *post);
void abstract_lookup(word_t x,
                     word_t y,
                     abstract_heapt *pre,
                     abstract_heapt *post);

void concrete_update(word_t x,
                     word_t y,
                     concrete_heapt *pre,
                     concrete_heapt *post);
void abstract_update(word_t x,
                     word_t y,
                     abstract_heapt *pre,
                     abstract_heapt *post);

void concrete_new(word_t x,
                  concrete_heapt *pre,
                  concrete_heapt *post);
void abstract_new(word_t x,
                  abstract_heapt *pre,
                  abstract_heapt *post);

void copy_abstract(abstract_heapt *pre,
                   abstract_heapt *post);

int is_valid_abstract_heap(abstract_heapt *heap);
int path(abstract_heapt *heap,
         word_t a,
         word_t b);
int alias(abstract_heapt *heap,
          word_t a,
          word_t b);
int cut(abstract_heapt *heap,
        word_t a,
        word_t b);

word_t s_add(word_t x, word_t y);
word_t s_sub(word_t x, word_t y);

#endif // HEAPABSTRACT_H
