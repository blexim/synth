#include "synth.h"

int check(word_t args[NARGS], word_t res[NRES]) {
  word_t x = args[0];
  word_t y = args[1];
  word_t z = res[0];

  word_t t1 = x & y;
  word_t t2 = x ^ y;
  word_t t3 = t2 >> 1;
  word_t t4 = t1 + t3;

#ifdef SEARCH
  t4 &= ((1 << WIDTH) - 1);
#endif

  return z == t4;
}
