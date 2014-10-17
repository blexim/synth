#include "synth.h"

int check(solution_t *solution, word_t args[1]) {
  word_t res[NRES];
  exec(&solution->progs[0], args, res);

  word_t x = args[0];
  word_t z = res[0];

  sword_t t1 = -x;
  word_t t2 = x & t1;

  if (t2 == 0) {
    return 1;
  }

  word_t t3 = x + t2;
  word_t t4 = x ^ t2;
  word_t t5 = t4 >> 2;

#ifdef SEARCH
  t5 &= WORDMASK;
#endif

  word_t t6 = t5 / t2;
  word_t t7 = t6 | t3;

#ifdef SEARCH
  t7 &= WORDMASK;
  z &= WORDMASK;
#endif

  return z == t7;
}
