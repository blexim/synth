#include "synth.h"

word_t checkit(solution_t *solution, word_t i, word_t j, word_t N) {
  word_t args[3];
  word_t res[1];

  args[0] = i;
  args[1] = j;
  args[2] = N;

  exec(&solution->progs[0], args, res);

  return res[0];
}

int check(solution_t *solution, word_t args[3]) {
  word_t i, j, N;

  j = args[1];
  N = args[2];

  if (j < N) {
    return 0;
  }

  i = 0;

  if (!checkit(solution, i, j, N)) {
    return 0;
  }

  i = args[0];

  if (checkit(solution, i, j, N) && i < j) {
    i++;

    if (!checkit(solution, i, j, N)) {
      return 0;
    }
  }

  i = args[0];

  if (checkit(solution, i, j, N) && i >= j) {
    if (i > N) {
      return 0;
    }
  }

  return 1;
}
