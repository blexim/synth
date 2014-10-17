#include "synth.h"

int check(solution_t *solution, word_t args[1]) {
  word_t res[NRES];
  exec(&solution->progs[0], args, res);

  word_t x = args[0];
  word_t z = res[0];
  word_t expected = 0;
  word_t bit;

  for (int i = 0; i < WIDTH; i++) {
    bit = x & 1;
    expected ^= bit;
    x >>= 1;
  }

  return expected == z;
}
