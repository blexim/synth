#include "heap.h"

const ptr_t x = 1;
const ptr_t y = 2;

int inv(heap_factst *facts, int n, int i) {
  return path_len(*facts, y, null_ptr) == (n - i) &&
         is_path(*facts, y, null_ptr);
}

int main(void) {
  abstract_heapt init_heap, tmp, pre_heap, post_heap;
  heap_factst f1, f2, f3;
  word_t n, i;
  word_t pre_i, pre_n, post_i;

  __CPROVER_assume(valid_abstract_heap(&init_heap));
  consequences(&init_heap, &f1);

  __CPROVER_assume(is_path(f1, x, null_ptr));
  __CPROVER_assume(alias(f1, x, y));

  n = path_len(f1, x, null_ptr);
  i = 0;
  assert(inv(&f1, n, i));

  __CPROVER_assume(valid_abstract_heap(&pre_heap));
  consequences(&pre_heap, &f2);

  __CPROVER_assume(inv(&f2, pre_n, pre_i) && pre_i < pre_n);

  assert(!alias(f2, y, null_ptr));

  abstract_lookup(&pre_heap, &post_heap, y, y);
  post_i = pre_i + 1;

  consequences(&post_heap, &f3);

  assert(inv(&f3, pre_n, post_i));
}
