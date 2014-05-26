#include "synth.h"

int check(solution_t *solution, word_t args[2]) {
  word_t res[1];
  exec(&solution->progs[0], args, res);

  word_t x = args[0];
  word_t y = args[1];
  word_t z = res[0];

  word_t t1 = x | y;
  word_t t2 = x ^ y;
  word_t t3 = t2 >> 1;
  word_t t4 = t1 - t3;

#ifdef SEARCH
  t4 &= ((1 << WIDTH) -1);
#endif

  return z == t4;
}
