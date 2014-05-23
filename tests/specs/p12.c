#include "synth.h"

int check(solution_t *solution, word_t args[2]) {
  word_t res[1];
  exec(&solution->prog, args, res);

  word_t x = args[0];
  word_t y = args[1];
  word_t z = res[0];

  word_t t1 = ~y;
  word_t t2 = x & t1;

  if (t2 <= y) {
    return !!z;
  } else {
    return !z;
  }
}
