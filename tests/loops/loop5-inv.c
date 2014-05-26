#include "synth.h"

word_t checkit(solution_t *solution, word_t i, word_t j, word_t x, word_t y) {
  word_t args[6];
  word_t res[1];

  args[0] = i;
  args[1] = j;
  args[2] = x;
  args[3] = y;
  args[4] = 0;
  args[5] = 0;

  exec(&solution->progs[0], args, res);

  return res[0];
}

int check(solution_t *solution, word_t args[6]) {
  int i, j, x, y;

  i = args[0];
  j = args[1];

  x = i;
  y = j;

  if (!checkit(solution, i, j, x, y)) {
    return 0;
  }

  x = args[2];
  y = args[3];

  if (!checkit(solution, i, j, x, y)) {
    return 1;
  }

  if (x == 0) {
    return 1;
  }

  x--;
  y--;

  if (!checkit(solution, i, j, x, y)) {
    return 0;
  }

  x = args[4];
  y = args[5];

  if (x != 0) {
    return 1;
  }

  if (checkit(solution, i, j, x, y)) {
    if (i == j) {
      if (y != 0) {
        return 0;
      }
    }
  }

  return 1;
}
