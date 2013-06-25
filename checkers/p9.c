#include "synth.h"

int check(word_t args[NARGS], word_t z) {
  word_t x = args[0];
  sword_t q = (sword_t) x;
  sword_t zero = 0;
  word_t ret;

  if (q < zero) {
    ret = -x;
  } else {
    ret = x;
  }

  return ret == z;
}
