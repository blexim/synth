#include "synth.h"

int check(solution_t *solution, word_t args[4]) {
  word_t res[NRES];
  exec(&solution->progs[0], args, res);

  word_t x = args[0];
  word_t a = args[1];
  word_t b = args[2];
  word_t c = args[3];
  word_t z = res[0];

  if (a == b || a == c || b == c) {
    return 1;
  }

  if (x == a) {
    return z == b;
  } else if (x == b) {
    return z == c;
  } else if (x == c) {
    return z == a;
  }

  return 1;
}
