#include "synth.h"

word_t inv(solution_t *solution, word_t i, word_t j, word_t a, word_t b, word_t flag) {
  word_t args[5];
  word_t res[1];

  args[0] = i;
  args[1] = j;
  args[2] = a;
  args[3] = b;
  args[4] = flag;

  exec(&solution->progs[0], args, res);

  return res[0] != 0;
}

int check(solution_t *solution, word_t args[5]) {
  word_t i, j, a, b, flag;

  flag = args[4];

  a = 0;
  b = 0;
  j = 1;

  if (flag) i = 0;
  else      i = 1;

  if (!inv(solution, i, j, a, b, flag)) {
    return 0;
  }

  i = args[0];
  j = args[1];
  a = args[2];
  b = args[3];

  if (inv(solution, i, j, a, b, flag)) {
    a++;
    b += (j - i);
    i += 2;

    if (i % 2 == 0) j += 2;
    else            j++;

    if (!inv(solution, i, j, a, b, flag)) {
      return 0;
    }
  }

  i = args[0];
  j = args[1];
  a = args[2];
  b = args[3];

  if (inv(solution, i, j, a, b, flag)) {
    if (flag) {
      if (a != b) {
        return 0;
      }
    }
  }

  return 1;
}
