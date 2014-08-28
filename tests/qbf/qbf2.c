#include "synth.h"

/*
 * exists(F) . exists(x) . forall(y) . x == y
 */

int check(solution_t *sol, word_t args[1]) {
  word_t x = sol->evars[0];
  word_t y = args[0];

  if (x != y) {
    return 0;
  }

  return 1;
}
