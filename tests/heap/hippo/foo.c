#include "heap.h"

ptr_t x = 1;
ptr_t p = 2;

int pre(abstract_heapt *pre, abstract_heapt *post) {
  return 1;
}

int cond(abstract_heapt *heap) {
  return 0;
}

int inv(abstract_heapt *heap) {
  return 1;
}

int body(abstract_heapt *pre, abstract_heapt *post) {
  return 1;
}

int assertion(abstract_heapt *heap) {
  return 0;
}
