#include "synth.h"

word_t acc(prog_t *prog, word_t x0, word_t k) {
  word_t args[3];
  word_t res[1];

  args[0] = x0;
  args[1] = k;
  args[2] = 0;
  args[3] = 0;

  exec(prog, args, res);

  return res[0];
}

int check(prog_t *prog, word_t args[4]) {
  int x0, x, x_, N, k;

  x0 = args[0];
  k = args[1];
  N = args[2];
  x = args[3];

  x_ = x + 1;

  if (x < N) {
    if (x == acc(prog, x0, k)) {
      if (x_ != acc(prog, x0, k+1)) {
        return 0;
      }
    }
  }

  x_ = x0 + 1;

  if (x0 < N) {
    if (x_ != acc(prog, x0, 1)) {
      return 0;
    }
  }

  return 1;
}
