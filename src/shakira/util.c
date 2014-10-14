#include <stdio.h>
#include <assert.h>
#include <string.h>

#include "heap.h"

/*
 * Saturating addition.
 */
word_t s_add(word_t x, word_t y) {
  word_t ret = (x > INF - y) ? INF : x + y;

  __CPROVER_assume(ret != INF || x == INF || y == INF);

  return ret;
}

/*
 * Saturating subtraction.
 */
word_t s_sub(word_t x, word_t y) {
  if (x == INF) {
    return INF;
  } else if (y > x) {
    return 0;
  } else {
    return x - y;
  }
}


#define LINEWIDTH 6
char *ptrnames[] = {"NULL", "x", "y", "z", "w", "q"};

void print_ptr(word_t p) {
  if (p < sizeof(ptrnames)) {
    printf("%s", ptrnames[p]);
  } else {
    printf("p%d", p);
  }
}

void print_len(word_t l) {
  if (l == INF) {
    printf("INF");
  } else {
    printf("%d", l);
  }
}

void print_concrete(concrete_heapt *heap) {
  int i;
  word_t y;

  printf("Successors:");

  for (i = 0; i < NNODES; i++) {
    if (i % LINEWIDTH == 0) {
      printf("\n");
    }

    y = heap->succ[i];

    printf("%d -> %d;   ", i, y);
  }

  printf("\nPointers:");

  for (i = 0; i < NPROG; i++) {
    if (i % LINEWIDTH == 0) {
      printf("\n");
    }

    y = heap->ptr[i];

    print_ptr(i); printf(" == %d;  ", y);
  }

  printf("\n");
}

void print_abstract_heap(abstract_heapt *heap) {

  printf("Heap contains %d nodes\n", heap->nnodes);

  printf("Successors:");

  node_t n, m;
  word_t len;

  for (n = 0; n < NABSNODES; n++) {
    if (n % LINEWIDTH == 0) {
      printf("\n");
    }

    m = heap->succ[n];
    len = heap->dist[n];

    printf("%d -", n); print_len(len); printf("-> %d    ", m);
  }

  printf("\nPointers:");

  ptr_t p;

  for (p = 0; p < NPROG; p++) {
    if (p % LINEWIDTH == 0) {
      printf("\n");
    }

    n = heap->ptr[p];

    print_ptr(p); printf(" == %d;  ", n);
  }

  printf("\n");
}

void print_facts(heap_factst *facts) {
  ptr_t p, q;
  word_t len;

  printf("Shortest paths:\n");

  for (p = 0; p < NPROG; p++) {
    for (q = 0; q < NPROG; q++) {
      len = facts->dists[p][q];
      print_ptr(p); printf(" -"); print_len(len); printf("-> "); print_ptr(q); printf("   ");
    }

    printf("\n");
  }
}

void serialize_facts(heap_factst *facts, word_t buf[NARGS]) {
  word_t i, j;

  for (i = 0; i < NPROG; i++) {
    for (j = 0; j < NPROG; j++) {
      buf[i*NPROG + j] = facts->dists[i][j];
    }
  }

  for (i = NPROG*NPROG; i < NARGS; i++) {
    buf[i] = 0;
  }
}

void deserialize_heap(word_t buf[NARGS], abstract_heapt *heap) {
  word_t i = 0;
  word_t j;

  for (j = 0; j < NABSNODES; j++) {
    heap->succ[j] = buf[i++];
  }

  for (j = 0; j < NABSNODES; j++) {
    heap->dist[j] = buf[i++];
  }

  for (j = 0; j < NPROG; j++) {
    heap->ptr[j] = buf[i++];
  }

  heap->nnodes = buf[i++];
}
