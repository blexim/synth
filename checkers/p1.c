#include "synth.h"

int check(word_t x, word_t z) {
  return z == ((x-1) & x);
}
