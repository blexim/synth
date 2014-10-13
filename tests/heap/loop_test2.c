#include "heap.h"

/*
 * List x, y;
 *
 * assume(path_len(x, null) == path_len(y, null))
 *
 * while (x != null) {
 *   x = x->n;
 *   y = y->n;
 * }
 * 
 * assert(y == null);
 *
 * Prove safety using invariant:
 *  path_len(y, null) == path_len(x, null)
 */

const ptr_t x = 1;
const ptr_t y = 2;

int inv(abstract_heapt *heap) {
  return path_len(heap, y, null_ptr) == path_len(heap, x, null_ptr);
}

int cond(abstract_heapt *heap) {
  return !alias(heap, x, null_ptr);
}

int assertion(abstract_heapt *heap) {
  return alias(heap, y, null_ptr);
}

int main(void) {
  abstract_heapt pre_heap, post_heap;
  abstract_heapt t1, t2;

  __CPROVER_assume(valid_abstract_heap(&pre_heap));
  __CPROVER_assume(inv(&pre_heap));
  __CPROVER_assume(cond(&pre_heap));

  abstract_lookup(&pre_heap, &t1, x, x);
  abstract_lookup(&t1, &t2, y, y);

  assert(inv(&t2));

  __CPROVER_assume(valid_abstract_heap(&post_heap));
  __CPROVER_assume(inv(&post_heap));
  __CPROVER_assume(!cond(&post_heap));

  assert(assertion(&post_heap));
}
