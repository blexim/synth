#include "synth.h"

int check(solution_t *solution, word_t args[1]) {
  word_t res[1];
  exec(&solution->prog, args, res);

  word_t x = args[0];
  word_t cnt = 0;
  word_t z = res[0];

  for (int i = 0; i < WIDTH; i++) {
    if (x & 1) {
      cnt++;
    }

    x >>= 1;
  }

  return cnt == z;
}
