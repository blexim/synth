#include "synth.h"

int check(prog_t *prog, word_t args[1]) {
  word_t res[1];
  exec(prog, args, res);

  word_t x = args[0];
  word_t z = res[0];
  word_t expected;
  word_t i;

  if ((x & (x-1)) == 0) {
    return z == x;
  }

  for (i = 0; i < WIDTH; i++) {
    if ((x >> i) == 1) {
      expected = (1 << (i+1));
      return z == expected;
    }
  }

  return z == 0;
}
