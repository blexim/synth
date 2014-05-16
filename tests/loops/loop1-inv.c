#include "synth.h"

int inv(prog_t *prog, word_t x) {
  word_t a[1];
  word_t res[1];

  a[0] = x;

  exec(prog, a, res);

  return res[0];
}

int check(prog_t *prog, word_t args[1]) {
  word_t x;

  x = 1;

  if (!inv(prog, x)) {
    return 0;
  }

  x = args[0];

  if (inv(prog, x)) {
    x += 2;

    if (!inv(prog, x)) {
      return 0;
    }
  }

  x = args[0];

  if (inv(prog, x)) {
    if (!(x % 2)) {
      return 0;
    }
  }

  return 1;
}
