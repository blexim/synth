#include "synth.h"

int check(word_t args[NARGS], word_t res[NRES]) {
  word_t x = args[0];
  word_t z = res[0];

  if (x & x+1) {
    return z;
  } else {
    return !z;
  }
}