#include "synth.h"

int check(prog_t *prog, word_t args[2]) {
  word_t res[1];
  word_t a[2];

  word_t x;

  x = 1;

  a[0] = x;
  a[1] = 0;
  exec(prog, a, res);

  if (res[0] == 0) {
    return 0;
  } else if (res[0] != 1) {
    return 0;
  }

  x = args[0];
  a[0] = x;
  exec(prog, a, res);

  if (res[0] == 0) {
    return 1;
  } else if (res[0] != 1) {
    return 0;
  }

  x += 2;

  a[0] = x;
  exec(prog, a, res);

  if (res[0] == 0) {
    return 0;
  } else if (res[0] != 1) {
    return 0;
  }

  x = args[1];
  a[0] = x;
  exec(prog, a, res);

  if (res[0] == 0) {
    return 1;
  } else if (res[0] != 1) {
    return 0;
  }

  if (x % 2) {
    return 1;
  }

  return 0;
}
