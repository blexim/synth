#include "synth.h"

int inv(solution_t *solution, word_t x, word_t i) {
  word_t a[2];
  word_t res[1];

  a[0] = x;
  a[1] = i;

  exec(&solution->progs[0], a, res);

  return res[0];
}

int check(solution_t *solution, word_t args[2]) {
  word_t x;
  word_t i;

  x = solution->evars[0];
  i = 0xf;

  if (!inv(solution, x, i)) {
    return 0;
  }

  x = args[0];
  i = args[1];

  if (i > 0 && inv(solution, x, i)) {
    i--;
    x += 2;

    if (!inv(solution, x, i)) {
      return 0;
    }
  }

  x = args[0];
  i = args[1];

  if (i <= 0 && inv(solution, x, i)) {
    if (x % 2) {
      return 0;
    }
  }

  return 1;
}
