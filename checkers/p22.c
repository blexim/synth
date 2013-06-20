#include "synth.h"

int check(word_t x, word_t z) {
  word_t ret = 0;

  for (int i = 0; i < WIDTH; i++) {
    ret ^= (x & 1);
    x >>= 1;
  }

  return ret == z;
}
