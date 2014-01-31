#include "synth.h"

int check(word_t args[NARGS], word_t res[NRES]) {
  word_t x = args[0];
  sword_t q = x;
  sword_t zero = 0;
  word_t expected;
  word_t z = res[0];

#ifdef SEARCH
  q <<= (32 - WIDTH);
  q >>= (32 - WIDTH);
#endif

  if (q == zero) {
    expected = 0;
  } else if (q < 0) {
    expected = -1;
  } else {
    expected = 1;
  }

#ifdef SEARCH
  expected &= ((1 << WIDTH) - 1);
#endif

  return expected == z;
}