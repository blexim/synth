#include "synth.h"

int check(word_t args[NARGS], word_t res[NRES]) {
  word_t x = args[0];
  sword_t q = (sword_t) x;
  sword_t zero = 0;
  word_t ret;
  word_t z = res[0];

#ifdef SEARCH
  q <<= (32-WIDTH);
  q >>= (32-WIDTH);
#endif

  if (q < zero) {
    ret = -x;
  } else {
    ret = x;
  }

  ret &= ((1 << WIDTH) - 1);

  return ret == z;
}
