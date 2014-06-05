#include "synth.h"

word_t rank(solution_t *solution, word_t x) {
  word_t args[1];
  word_t res[3];

  args[0] = x;

  exec(&solution->progs[0], args, res);

  return res[0];
}

word_t inv1(solution_t *solution, word_t x) {
  word_t args[1];
  word_t res[3];

  args[0] = x;

  exec(&solution->progs[1], args, res);

  return res[0];
}

word_t inv2(solution_t *solution, word_t x) {
  word_t args[1];
  word_t res[3];

  args[0] = x;

  exec(&solution->progs[2], args, res);

  return res[0];
}

int check(solution_t *solution, word_t args[1]) {
  word_t x;

  x = args[0];

  if (!inv1(solution, 0)) {
    return 0;
  }

  if (inv1(solution, x) && x < 9) {
    x++;

    if (!inv1(solution, x)) {
      return 0;
    }
  }

  x = args[0];

  if (inv1(solution, x) && x >= 9) {
    if (!inv2(solution, x)) {
      return 0;
    }
  }

  if (inv2(solution, x) && (x != 1)) {
    word_t r1 = rank(solution, x);

    if (r1 <= 0) {
      return 0;
    }

    x -= 2;

    word_t r2 = rank(solution, x);

    if (r1 <= r2) {
      return 0;
    }

    if (!inv2(solution, x)) {
      return 0;
    }
  }

  return 1;
}
