#include "synth.h"

int check(word_t args[NARGS], word_t res[NRES]) {
  word_t x = args[0];
  word_t q = ((x-1) & (~x));
  word_t z = res[0];

#ifdef SEARCH
  q &= ((1 << WIDTH) - 1);
#endif

  return q == z;
}
