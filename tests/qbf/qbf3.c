#include "synth.h"

/*
 * forall(x, y) . exists(z) . x + z == y
 */

int check(solution_t *sol, word_t args[2]) {
  word_t x = args[0];
  word_t y = args[1];

  word_t res[NRES];

  exec(&sol->progs[0], args, res);
  word_t z = res[0];
  word_t q = x + z;

  q &= WORDMASK;

  if (q != y) {
    return 0;
  }

  return 1;
}
