#include "synth.h"

int check(word_t args[NARGS], word_t z) {
  word_t x = args[0];
  word_t q = x;

  q--;

  return z == (q | x);
}
