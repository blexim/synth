#include "heapabstract.h"
#include "heap_axioms.h"

/*
 * assume(len(x, null) == len(y, null));
 *
 * while (x != null && y != null) {
 *   assert(y != null);
 *
 *   x = x->n;
 *   y = y->n;
 * }
 */

word_t x = 1;
word_t y = 2;

int cond(abstract_heapt *heap) {
  return !alias(heap, x, nil) && !alias(heap, y, nil);
}

int inv(abstract_heapt *heap) {
  return heap->dist[x][nil] == heap->dist[y][nil] &&
         path(heap, x, nil);
}

int body(abstract_heapt *pre,
         abstract_heapt *post) {
  abstract_heapt tmp;

  abstract_lookup(x, x, pre, &tmp);
  abstract_lookup(y, y, &tmp, post);
}

int axioms(abstract_heapt *heap) {
  return path_axioms(heap) &&
         alias_axioms(heap) &&
         cycle_axioms(heap) &&
         null_axioms(heap);
}

int main(void) {
  abstract_heapt pre_heap, t, post_heap;

  __CPROVER_assume(axioms(&pre_heap));
  __CPROVER_assume(inv(&pre_heap) && cond(&pre_heap));
  body(&pre_heap, &t);
  __CPROVER_assume(abstractions_equal(&t, &post_heap));
  __CPROVER_assume(axioms(&post_heap));
  assert(inv(&post_heap));
}
