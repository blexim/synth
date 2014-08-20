#include "heaplib.h"

int path(word_t x, word_t y, word_t vars[NARGS]) {
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
  //assume(is_ptr(p));
  return vars[p - 1];
}
