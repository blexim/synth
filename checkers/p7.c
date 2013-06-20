#include "synth.h"

int check(word_t x, word_t z) {
  word_t q = ((~x) & (x+1));

  return z == q;
}
