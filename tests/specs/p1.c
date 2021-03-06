#include "synth.h"

int check(solution_t *solution, word_t args[1]) {
  word_t res[NRES];
  exec(&solution->progs[0], args, res);

  word_t x = args[0];
  word_t z = res[0];
  word_t expected = (x-1) & x;

#ifdef SEARCH
  z &= WORDMASK;
  expected &= WORDMASK;
#endif

  return z == expected;
}
