#include "synth.h"

int check(solution_t *solution, word_t args[2]) {
  word_t res[NRES];
  exec(&solution->progs[0], args, res);

  word_t x = args[0];
  word_t y = args[1];
  word_t t1 = ~y;
  word_t t2 = x & t1;
  word_t z = res[0];

#ifdef SEARCH
  t2 &= WORDMASK;
  y &= WORDMASK;
#endif

  if (t2 > y) {
    return !!z;
  } else {
    return !z;
  }
}
