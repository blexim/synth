#include "synth.h"

int check(word_t x, word_t z) {
  sword_t q = x;
  word_t res;

  if (x == 0) {
    res = 0;
  } else if (q < 0) {
    res = -1;
  } else {
    res = 1;
  }

  return res == z;
}
