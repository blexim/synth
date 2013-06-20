#include "synth.h"

int check(word_t x, word_t z) {
  word_t t1 = -x;
  word_t t2 = x & t1;
  word_t t3 = x + t2;
  word_t t4 = x ^ t2;
  word_t t5a = t2 >> 1;
  word_t t5 = t5 >> 1;
  word_t t6 = t5 / t2;
  word_t t7 = t6 | t3;

  return z == t7;
}
