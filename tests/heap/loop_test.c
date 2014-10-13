#include "heap.h"

/*
 * List y = x;
 * int n = path_len(x, null);
 * int i;
 *
 * while (i < n) {
 *   y = y->n;
 * }
 *
 * Prove safety using invariant:
 *  path_len(y, null) == (n - i) && is_path(y, null)
 */

const ptr_t x = 1;
const ptr_t y = 2;

int inv(abstract_heapt *heap, int n, int i) {
  word_t y_null = path_len(heap, y, null_ptr);

  return y_null == (n - i) && y_null != INF;
}

int main(void) {
  abstract_heapt init_heap, tmp, pre_heap, post_heap;
  heap_factst f1, f2, f3;
  word_t n, i;
  word_t pre_i, pre_n, post_i;

  __CPROVER_assume(valid_abstract_heap(&init_heap));

  word_t x_null = path_len(&init_heap, x, null_ptr);
  __CPROVER_assume(x_null != INF);
  __CPROVER_assume(alias(&init_heap, x, y));

  n = x_null;
  i = 0;
  assert(inv(&init_heap, n, i));

  __CPROVER_assume(valid_abstract_heap(&pre_heap));

  __CPROVER_assume(inv(&pre_heap, pre_n, pre_i) && pre_i < pre_n);

  assert(!alias(&pre_heap, y, null_ptr));

  abstract_lookup(&pre_heap, &post_heap, y, y);
  post_i = pre_i + 1;

  assert(inv(&post_heap, pre_n, post_i));
}
