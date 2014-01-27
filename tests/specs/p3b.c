#include "synth.h"

int check(word_t args[NARGS], word_t res) {
  word_t x = args[0];
  word_t z = 1;

  if (x == 0) {
    return (res == 0);
  }

  for (int i = 0; i < WIDTH; i++) {
    if (z & x) {
      return res == z;
    }

    z <<= 1;
  }

  // NOTREACHED
  return 0;
}
