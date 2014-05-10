#include "synth.h"

int check(prog_t *prog, word_t args[1]) {
  word_t res[1];
  exec(prog, args, res);

  word_t x = args[0];
  word_t z = res[0];
  word_t expected = (x-1) & x;

  return z == expected;
}
