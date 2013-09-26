#include "synth.h"

int check(word_t args[NARGS], word_t res[NRES]) {
  word_t x = args[0];
  word_t m = args[1];
  word_t k = args[2];
  word_t z = res[0];

  word_t t1 = x >> k;
  word_t t2 = x ^ t1;
  word_t t3 = t2 & m;
  word_t t4 = t3 << k;
  word_t t5 = t4 ^ t3;
  word_t t6 = t5 ^ x;

  return t6 == z;
}
