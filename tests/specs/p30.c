#include "synth.h"

int check(solution_t *solution, word_t args[1]) {
  word_t res[1];

  exec(&solution->progs[0], solution->evars, res);

  if (res[0] != 1) {
    return 0;
  }

  exec(&solution->progs[0], args, res);

  if (res[0] != args[0]) {
    return 0;
  }

  return 1;
}
