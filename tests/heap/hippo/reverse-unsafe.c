#include "heap.h"

ptr_t root = 1;
ptr_t new_root = 2;
ptr_t next = 3;

int pre(abstract_heapt *pre, abstract_heapt *post) {
  *post = *pre;
  return is_null(post, new_root);
}

int cond(abstract_heapt *heap) {
  return !is_null(heap, root);
}

int body(abstract_heapt *pre, abstract_heapt *post) {
  if (is_null(pre, root)) {
    return 0;
  }

  abstract_heapt t1, t2, t3, t4;

  abstract_lookup(pre, &t1, next, root);

  if (is_null(&t1, root)) {
    return 0;
  }

  abstract_lookup(&t1, &t2, root, root);

  if (is_null(&t2, root)) {
    return 0;
  }

  abstract_update(&t2, &t3, root, new_root);
  abstract_assign(&t3, &t4, new_root, root);
  abstract_assign(&t4, post, root, next);

  return 1;
}

int assertion(abstract_heapt *heap) {
  return is_path(heap, new_root, null_ptr);
}

word_t rank1(abstract_heapt *heap) {
  return 1;
}

word_t rank2(abstract_heapt *heap) {
  return 1;
}

int init(abstract_heapt *heap) {
  return path_len(heap, root, null_ptr) == 1;
}

int danger(abstract_heapt *heap) {
  return path_len(heap, root, null_ptr) == 1;
}
