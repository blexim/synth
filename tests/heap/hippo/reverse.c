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

  abstract_heapt t1, t2, t3;

  abstract_lookup(pre, &t1, next, root);

  if (is_null(&t1, root)) {
    return 0;
  }

  abstract_update(&t1, &t2, root, new_root);
  abstract_assign(&t2, &t3, new_root, root);
  abstract_assign(&t3, post, root, next);

  return 1;
}

int assertion(abstract_heapt *heap) {
  return is_path(heap, new_root, null_ptr);
}

int inv(abstract_heapt *heap) {
  return is_path(heap, new_root, null_ptr);
}
