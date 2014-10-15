#include "heap.h"

void copy_concrete(concrete_heapt *pre,
                   concrete_heapt *post) {
  int i;

  for (i = 0; i < NNODES; i++) {
    post->succ[i] = pre->succ[i];
    post->ptr[i] = pre->ptr[i];
  }
}

void concrete_assign(concrete_heapt *pre,
                     concrete_heapt *post,
                     ptr_t x,
                     ptr_t y) {
  copy_concrete(pre, post);
  post->ptr[x] = pre->ptr[y];
}

void concrete_lookup(concrete_heapt *pre,
                     concrete_heapt *post,
                     ptr_t x,
                     ptr_t y) {
  word_t py = pre->ptr[y];
  word_t yn = pre->succ[py];

  __CPROVER_assume(py != 0);

  copy_concrete(pre, post);
  post->ptr[x] = yn;
}

void concrete_update(concrete_heapt *pre,
                     concrete_heapt *post,
                     ptr_t x,
                     ptr_t y) {
  word_t py = pre->ptr[y];
  word_t px = pre->ptr[x];

  __CPROVER_assume(px != 0);

  copy_concrete(pre, post);
  post->succ[px] = py;
}

int named_node(concrete_heapt *heap, node_t n) {
  ptr_t p;

  for (p = 0; p < NPROG; p++) {
    if (heap->ptr[p] == n) {
      return 1;
    }
  }

  return 0;
}

int has_predecessor(concrete_heapt *heap, node_t n) {
  node_t m;

  for (m = 0; m < NNODES; m++) {
    if (heap->succ[m] == n) {
      return 0;
    }
  }
  return 1;
}

void concrete_new(concrete_heapt *pre,
                  concrete_heapt *post,
                  ptr_t x) {
  node_t new_node = null_node;
  word_t n;

  /* search for an anonymous node without incoming edges and whose successor is null */
  for(n = 0; n < NNODES; n++) {
    if(!named_node(pre, n) && !has_predecessor(pre, n)) {
      new_node = n;
    }
  }

  // we'll use this node as the new allocated node
  __CPROVER_assume(new_node != null_node); 

  copy_concrete(pre, post);
  post->ptr[x] = new_node;
  post->succ[x] = null_node;
}
