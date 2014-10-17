#include "synth.h"

int check(solution_t *solution, word_t args[2]) {
  word_t res[NRES];
  exec(&solution->progs[0], args, res);

  word_t x = args[0];
  word_t y = args[1];
  word_t z = res[0];

  if (x > y) {
    return z == x;
  } else {
    return z == y;
  }
}
