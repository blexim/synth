#include "synth.h"

int check(word_t args[NARGS], word_t res[NRES]) {
  word_t x = args[0];
  word_t q = x;
  word_t z = res[0];
  q--;

  return (z == (q ^ x));
}
