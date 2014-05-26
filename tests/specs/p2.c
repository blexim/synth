#include "synth.h"

int check(solution_t *solution, word_t args[1]) {
  word_t res[1];
  exec(&solution->progs[0], args, res);

  word_t x = args[0];
  word_t z = res[0];

  if (x & x+1) {
    return z;
  } else {
    return !z;
  }
}
