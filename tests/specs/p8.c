#include "synth.h"

int check(solution_t *solution, word_t args[1]) {
  word_t res[NRES];
  exec(&solution->progs[0], args, res);

  word_t x = args[0];
  word_t q = ((x-1) & (~x));
  word_t z = res[0];

#ifdef SEARCH
  q &= WORDMASK;
  z &= WORDMASK;
#endif

  return q == z;
}
