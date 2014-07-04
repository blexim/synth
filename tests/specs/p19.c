#include "synth.h"

int check(solution_t *solution, word_t args[3]) {
  word_t res[NRES];
  exec(&solution->progs[0], args, res);

  word_t x = args[0];
  word_t m = args[1];
  word_t k = args[2];
  word_t z = res[0];

  if (k >= WIDTH) {
    return 1;
  }

  if (m >= (1 << (WIDTH - k - 1))) {
    return 1;
  }

  if (m == 0) {
    return 1;
  }

  word_t t1 = x >> k;
  word_t t2 = x ^ t1;
  word_t t3 = t2 & m;
  word_t t4 = t3 << k;
  word_t t5 = t4 ^ t3;
  word_t t6 = t5 ^ x;

  return z == t6;
}
