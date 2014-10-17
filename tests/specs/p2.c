#include "synth.h"

int check(solution_t *solution, word_t args[NARGS]) {
  word_t res[NRES];
  exec(&solution->progs[0], args, res);

  word_t x = args[0];
  word_t z = res[0];

  if (x & x+1) {
    return z != 0;
  } else {
    return z == 0;
  }
}
