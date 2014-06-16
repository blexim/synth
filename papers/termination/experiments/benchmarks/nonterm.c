#include "synth.h"

int inv(prog_t *prog, word_t x) {
  word_t args[1];
  word_t ret[NRES];

  args[0] = x;

  exec(prog, &x, ret);

  return ret[0];
}

int check(solution_t *sol, word_t args[2]) {
  word_t x;
  word_t z = sol->evars[0];
  prog_t *prog = &sol->progs[0];

  if (!inv(prog, z) || z == 0) {
    return 0;
  }

  x = args[0];

  if (inv(prog, x) && x != 0) {
    x = x + 2;

    if (!inv(prog, x)) {
      return 0;
    }

    if (x == 0) {
      return 0;
    }
  }

  return 1;
}
