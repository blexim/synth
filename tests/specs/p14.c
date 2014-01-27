#include "synth.h"

int check(word_t args[NARGS], word_t res[NRES]) {
  word_t x = args[0];
  word_t y = args[1];
  word_t z = res[0];
  word_t z2 = 2 * z;
  word_t sum = x + y;
  word_t sum_minus_1 = sum - 1;

  if ((z <= x && z >= y) || (z <= y && z >= x)) {
    if ((z2 == sum) || (z2 == sum_minus_1)) {
      return 1;
    }
  }

  return 0;
}
