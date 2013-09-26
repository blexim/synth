#include "synth.h"

int check(word_t args[NARGS], word_t res[NRES]) {
  word_t x = args[0];
  word_t z = res[0];
  word_t expected;
  word_t i;

  if ((x & (x-1)) == 0) {
    return z == x;
  }

  for (i = 0; i < WIDTH; i++) {
    if ((x >> i) == 1) {
      expected = (1 << (i+1));
      return z == expected;
    }
  }

  return z == 0;
}
