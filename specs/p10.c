#include "synth.h"

int check(word_t args[NARGS], word_t z) {
  word_t x = args[0];
  word_t y = args[1];

  if ((x ^ y) <= (x & y)) {
    return !!z;
  } else {
    return !z;
  }
}
