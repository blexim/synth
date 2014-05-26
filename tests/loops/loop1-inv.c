#include "synth.h"

int inv(solution_t *solution, word_t x) {
  word_t a[1];
  word_t res[1];

  a[0] = x;

  exec(&solution->progs[0], a, res);

  return res[0];
}

int check(solution_t *solution, word_t args[1]) {
  word_t x;

  x = 1;

  if (!inv(solution, x)) {
    return 0;
  }

  x = args[0];

  if (inv(solution, x)) {
    x += 2;

    if (!inv(solution, x)) {
      return 0;
    }
  }

  x = args[0];

  if (inv(solution, x)) {
    if (!(x % 2)) {
      return 0;
    }
  }

  return 1;
}
