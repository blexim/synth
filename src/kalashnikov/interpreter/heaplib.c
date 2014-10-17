#include "heaplib.h"

int is_path(word_t x, word_t y, word_t vars[NARGS]) {
  int i = 0;

  while (x != 0 && x != y && i++ < NARGS) {
    x = deref(x, vars);
  }

  return x == y;
}

int is_ptr(word_t p) {
  return p >= 0 && p <= NARGS;
}

word_t deref(word_t p, word_t vars[NARGS]) {
  assume2(is_ptr(p) && p != 0);
  return vars[p - 1];
}
