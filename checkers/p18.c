#include "synth.h"

int check(word_t x, word_t z) {
  word_t res;

  if (x == 0) {
    res = 0;
  } else {
    word_t q = ((x+1) & x);

    if (q == x) {
      res = 1;
    } else {
      res = 0;
    }
  }

  return res == z;
}
