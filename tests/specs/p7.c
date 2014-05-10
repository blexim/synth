#include "synth.h"

int check(prog_t *prog, word_t args[1]) {
  word_t res[1];
  exec(prog, args, res);

  word_t x = args[0];
  word_t q = ((~x) & (x+1));
  word_t z = res[0];

#ifdef SEARCH
  q &= ((1 << WIDTH) - 1);
#endif

  return z == q;
}
