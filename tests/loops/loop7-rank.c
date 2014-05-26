#include "synth.h"

word_t rank(solution_t *solution, word_t x, word_t N) {
  word_t args[2];
  word_t res[1];

  args[0] = x;
  args[1] = N;

  exec(&solution->progs[0], args, res);

  return res[0];
}

int check(solution_t *solution, word_t args[2]) {
  int x, x_, N;

  x = args[0];
  N = args[1];

  x_ = x + 1;

  if (x < N) {
    if (rank(solution, x, N) <= 0) {
      return 0;
    }

    if (rank(solution, x, N) <= rank(solution, x_, N)) {
      return 0;
    }
  }

  return 1;
}
