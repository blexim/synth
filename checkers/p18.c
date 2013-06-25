#include "synth.h"

int check(word_t args[NARGS], word_t z) {
  word_t x = args[0];
  word_t res;

  if (x == 0) {
    return !z;
  } else {
    word_t q = ((x+1) & x);

    if (q == x) {
      return !!z;
    } else {
      return !z;
    }
  }
}
