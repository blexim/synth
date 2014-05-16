#include "synth.h"
#include "exec.h"

word_t checkit(prog_t *prog, word_t x, word_t y) {
  word_t args[5];
  word_t res[1];

  args[0] = x;
  args[1] = y;
  args[2] = 0;

  exec(prog, args, res);

  return res[0] != 0;
}

int check(prog_t *prog, word_t args[3]) {
  word_t x, y, taken;

  x = 0;
  y = 0;

  if (!checkit(prog, x, y)) {
    return 0;
  }

  x = args[0];
  y = args[1];
  taken = args[2];

  if (checkit(prog, x, y) &&
      x < 50 &&
      y < 50) {
    if (taken) {
      x++;
      y += 10;
    } else {
      if (x >= 4) {
        x++;
        y++;
      }
    }

    if (!checkit(prog, x, y)) {
      return 0;
    }
  }

  x = args[0];
  y = args[1];

  if (x < 50 && y >= 50 && checkit(prog, x, y)) {
    if (x > y || y > 10*x) {
      return 0;
    }
  }

  return 1;
}
