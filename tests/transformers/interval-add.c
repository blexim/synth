#include "synth.h"

int check(prog_t *prog, word_t args[6]) {
  // Abstract transformer for z = x + y
  // looking for a transformer: [z-, z+] = [x-, x+] + [y-, y+]
  word_t xl = args[0];
  word_t xh = args[1];
  word_t x  = args[2];
  word_t yl = args[3];
  word_t yh = args[4];
  word_t y  = args[5];
  word_t z = x + y;

  word_t res[2];
  args[2] = 0;
  args[5] = 0;

  if (x < xl || x > xh) {
    return 1;
  }

  if (y < yl || y > yh) {
    return 1;
  }

  exec(prog, args, res);

  word_t zl = res[0];
  word_t zh = res[1];

  if (z < zl || z > zh) {
    return 0;
  }

  return 1;
}
