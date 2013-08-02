#include "synth.h"

int check(word_t args[NARGS], word_t z) {
  word_t x = args[0];
  word_t cnt = 0;

  for (int i = 0; i < WIDTH; i++) {
    if (x & 1) {
      cnt++;
    }

    x >>= 1;
  }

  return cnt == z;
}
