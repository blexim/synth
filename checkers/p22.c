#include "synth.h"

int check(word_t args[NARGS], word_t z) {
  word_t x = args[0];
  word_t ret = 0;

  for (int i = 0; i < WIDTH; i++) {
    ret ^= (x & 1);
    x >>= 1;
  }

  return ret == z;
}
