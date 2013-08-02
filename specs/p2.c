#include "synth.h"

int check(word_t args[NARGS], word_t z) {
  word_t x = args[0];

  if (x & x+1) {
    return z;
  } else {
    return !z;
  }
}
