#include "synth.h"

int check(word_t args[NARGS], word_t z) {
  word_t x = args[0];

  sword_t t1 = -x;
  word_t t2 = x & t1;
  word_t t3 = x + t2;
  word_t t4 = x ^ t2;
  word_t t5 = t4 >> 2;
  word_t t6 = t5 / t2;
  word_t t7 = t6 | t3;

  return z == t7;
}
