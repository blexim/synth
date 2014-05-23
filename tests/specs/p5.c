#include "synth.h"

int check(solution_t *solution, word_t args[1]) {
  word_t res[1];
  exec(&solution->prog, args, res);

  word_t x = args[0];
  word_t z = res[0];
  word_t q = x - 1;

#ifdef SEARCH
  q &= ((1 << WIDTH) - 1);
#endif

  return z == (q | x);
}
