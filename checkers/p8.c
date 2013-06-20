#include "synth.h"

int check(word_t x, word_t z) {
  word_t q = ((x-1) & (~x));

  return q == z;
}
