#include "synth.h"

word_t checkit(prog_t *prog, word_t x, word_t y) {
  word_t args[4];
  word_t res[1];

  args[0] = x;
  args[1] = y;
  args[2] = 0;
  args[3] = 0;

  exec(prog, args, res);

  return res[0];
}

int check(prog_t *prog, word_t args[4]) {
  int x, y;

  x = 0;
  y = 0;

  if (!checkit(prog, x, y)) {
    return 0;
  }

  x = args[0];
  y = args[1];

  if (!checkit(prog, x, y)) {
    return 1;
  }

    x++;
    y++;

  if (!checkit(prog, x, y)) {
    return 0;
  }

  x = args[2];
  y = args[3];

  if (checkit(prog, x, y)) {
    if (x != y) {
      return 0;
    }
  }

  return 1;
}
