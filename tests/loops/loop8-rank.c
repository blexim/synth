#include "synth.h"

#define WORDMASK ((1 << WIDTH) - 1)

word_t rank(prog_t *prog, word_t x, word_t y) {
  word_t args[5];
  word_t res[1];

  args[0] = x;
  args[1] = y;
  args[2] = 0;
  args[3] = 0;
  args[4] = 0;

  exec(prog, args, res);

  return res[0];
}

int check(prog_t *prog, word_t args[5]) {
  int a, b, x, y, x_, y_, taken;

  a = args[0];
  b = args[1];
  x = args[2];
  y = args[3];
  taken = args[4];

  x_ = x;
  y_ = y;

  if (x > 0 && y > 0) {
    if (taken) {
      x_--;
      y_++;

      y_ &= WORDMASK;
    } else {
      y_--;
    }

    if (rank(prog, x, y) <= 0) {
      return 0;
    }

    if (rank(prog, x, y) <= rank(prog, x_, y_)) {
      return 0;
    }
  }

  return 1;
}
