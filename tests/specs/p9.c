#include "synth.h"

int check(solution_t *solution, word_t args[1]) {
  word_t res[1];
  exec(&solution->prog, args, res);

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
