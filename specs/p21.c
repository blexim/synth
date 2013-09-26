#include "synth.h"

int check(word_t args[NARGS], word_t res[NRES]) {
  word_t x = args[0];
  word_t a = args[1];
  word_t b = args[2];
  word_t c = args[3];
  word_t z = res[0];

  word_t t1 = x != c;
  word_t t2 = a ^ c;
  word_t t3 = x != a;
  word_t t4 = b ^ c;
  word_t t5 = t1 & t2;
  word_t t6 = t3 & t4;
  word_t t7 = t5 ^ t6;
  word_t t8 = t7 ^ c;

  return z == t8;
}
