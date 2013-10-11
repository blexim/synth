#include "synth.h"

int check(word_t args[2], word_t res[1]) {
  word_t x = args[0];
  word_t y = args[1];
  word_t z = res[0];

  if (x <= y) {
    return x == z;
  } else {
    return y == z;
  }
}
