#include "synth.h"

int check(solution_t *solution, word_t args[2]) {
  word_t res[NRES];
  exec(&solution->progs[0], args, res);

  word_t x = args[0];
  word_t k = args[1];
  word_t z = res[0];

  word_t t1 = (-1 >> k);
  word_t t2 = t1 + 1;
  word_t t3 = x - t2;
  word_t t4 = t3 & t1;

#ifdef SEARCH
  t4 &= WORDMASK;
#endif

  return z == t4;
}
