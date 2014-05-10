#include "synth.h"

word_t checkit(prog_t *prog, word_t i, word_t j, word_t a, word_t b, word_t flag) {
  word_t args[9];
  word_t res[1];

  args[0] = i;
  args[1] = j;
  args[2] = a;
  args[3] = b;
  args[4] = flag;
  args[5] = 0;
  args[6] = 0;
  args[7] = 0;
  args[8] = 0;

  exec(prog, args, res);

  return res[0];
}

int check(prog_t *prog, word_t args[9]) {
  word_t i, j, a, b, flag;

  flag = args[4];

  if (flag != 1) {
    return 1;
  }

  a = 0;
  b = 0;
  j = 1;

  if (flag) i = 0;
  else      i = 1;

  if (!checkit(prog, i, j, a, b, flag)) {
    return 0;
  }

  i = args[0];
  j = args[1];
  a = args[2];
  b = args[3];

  if (!checkit(prog, i, j, a, b, flag)) {
    return 1;
  }

    a++;
    b += (j - i);
    i += 2;

    if (i % 2 == 0) j += 2;
    else            j++;

  if (!checkit(prog, i, j, a, b, flag)) {
    return 0;
  }

  i = args[5];
  j = args[6];
  a = args[7];
  b = args[8];

  if (checkit(prog, i, j, a, b, flag)) {
    if (flag) {
      if (a != b) {
        return 0;
      }
    }
  }

  return 1;
}
