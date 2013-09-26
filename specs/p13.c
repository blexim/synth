#include "synth.h"

int check(word_t args[NARGS], word_t res[NRES]) {
  word_t x = args[0];
  sword_t q = x;
  sword_t zero = 0;
  word_t expected;
  word_t z = res[0];

  if (q == zero) {
    expected = 0;
  } else if (q < 0) {
    expected = -1;
  } else {
    expected = 1;
  }

  return expected == z;
}
