#include "synth.h"

int check(word_t args[NARGS], word_t z) {
  word_t x = args[0];

  for (int i = 0; i < WIDTH; i++) {
    if (x == 0) {
      return z == 0;
    }

    if (x == 1) {
      return z == 1;
    } else if (x & 1) {
      return z == 0;
    }

    x >>= 1;
  }

  return 0;
}
