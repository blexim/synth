#include "synth.h"

int check(prog_t *prog, word_t args[2]) {
  word_t res[1];
  exec(prog, args, res);

  word_t x = args[0];
  word_t k = args[1];
  word_t z = res[0];

  word_t t1 = (-1 >> k);
  word_t t2 = t1 + 1;
  word_t t3 = x - t2;
  word_t t4 = t3 & t1;

#ifdef SEARCH
  t4 &= ((1 << WIDTH) - 1);
#endif

  return z == t4;
}
