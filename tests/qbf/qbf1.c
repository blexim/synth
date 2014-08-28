#include "synth.h"

/*
 * exists(F) . forall(x) . exists(y) . x == y
 */

int check(solution_t *sol, word_t args[1]) {
  word_t x = args[0];
  word_t res[NRES];

  exec(&sol->progs[0], args, res);
  word_t y = res[0];

  if (x != y) {
    return 0;
  }

  return 1;
}
