#include "synth.h"

int check(prog_t *prog, word_t args[1]) {
  word_t res[1];
  exec(prog, args, res);

  word_t x = args[0];
  word_t z = res[0];

  for (int i = 0; i < WIDTH; i++) {
    if (x == 0) {
      return z == 0;
    }

    if (x == 1) {
      return z == 1;
    } else if (x & 1) {
      return z == 0;
    }

    x >>= 1;
  }

  return 0;
}
