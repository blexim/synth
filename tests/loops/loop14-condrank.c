#include "synth.h"

word_t rank(solution_t *solution, word_t x, word_t y) {
  word_t args[2];
  word_t res[1];

  args[0] = x;
  args[1] = y;

  exec(&solution->progs[0], args, res);

  return res[0];
}

word_t inv(solution_t *solution, word_t x, word_t y) {
  word_t args[2];
  word_t res[1];

  args[0] = x;
  args[1] = y;

  exec(&solution->progs[1], args, res);

  return res[0];
}

int check(solution_t *solution, word_t args[2]) {
  word_t x, y;

  x = args[0];
  y = 1;

  if (!inv(solution, x, y)) {
    return 0;
  }

  x = args[0];
  y = args[1];

  if (inv(solution, x, y) && x > 0) {
    word_t r1 = rank(solution, x, y);

    if (r1 <= 0) {
      return 0;
    }

    x -= y;

    word_t r2 = rank(solution, x, y);

    if (r1 <= r2) {
      return 0;
    }

    if (!inv(solution, x, y)) {
      return 0;
    }
  }

  return 1;
}
