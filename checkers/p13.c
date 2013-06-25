#include "synth.h"

int check(word_t args[NARGS], word_t z) {
  word_t x = args[0];
  sword_t q = x;
  sword_t zero = 0;
  word_t res;

  if (q == zero) {
    res = 0;
  } else if (q < 0) {
    res = -1;
  } else {
    res = 1;
  }

  return res == z;
}
