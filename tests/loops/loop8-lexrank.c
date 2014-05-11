#include "synth.h"

#define WORDMASK ((1 << WIDTH) - 1)

int check(prog_t *prog, word_t args[3]) {
  word_t a[3];
  int x, y, x_, y_, taken;
  int i;

  for (i = 0; i < SZ; i++) {
    if (prog->params[i*2] == CONSTS + 2 ||
        prog->params[(i*2)+1] == CONSTS + 2) {
      //return 0;
    }
  }

  x = args[0];
  y = args[1];
  taken = args[2];

  if (taken != 0 && taken != 1) {
    return 1;
  }

  if (x > 0 && y > 0) {
    if (taken == 1) {
      x_ = x - 1;
      y_ = y + 1;
    } else {
      y_ = y - 1;
    }

    a[0] = x;
    a[1] = y;
    a[2] = 0;

    word_t rank1[2];
    exec(prog, args, rank1);

    if (rank1[0] < 0 ||
        (rank1[0] == 0 && rank1[1] <= 0)) {
      return 0;
    }

    a[0] = x_;
    a[1] = y_;

    word_t rank2[2];
    exec(prog, args, rank2);

    if (rank1[0] < rank2[0] ||
        (rank1[0] == rank2[0] && rank1[1] <= rank2[1])) {
      return 0;
    }
  }

  return 1;
}
