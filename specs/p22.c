#include "synth.h"

int check(word_t args[NARGS], word_t res[NRES]) {
  word_t x = args[0];
  word_t res = 0;
  word_t bit;
  word_t z = res[0];

  for (int i = 0; i < WIDTH; i++) {
    bit = x & 1;
    res ^= bit;
    x >>= 1;
  }

  return res == z;
}
