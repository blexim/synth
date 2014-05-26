#include "synth.h"

#define WORDMASK ((1 << WIDTH) - 1)

int check(solution_t *solution, word_t args[3]) {
  word_t a[3], b[3];
  word_t rank1[2], rank2[2];
  int x, y, x_, y_, taken;
  int i;

  x = args[0];
  y = args[1];
  taken = args[2];

  if (x > 0 && y > 0) {
    if (taken) {
      x_ = x - 1;
      y_ = y + 1;
    } else {
      x_ = x;
      y_ = y - 1;
    }

    a[0] = x;
    a[1] = y;
    a[2] = 0;
    exec(&solution->progs[0], a, rank1);

    if (rank1[0] == 0 || rank1[1] == 0) {
      return 0;
    }

    b[0] = x_;
    b[1] = y_;
    b[2] = 0;
    exec(&solution->progs[0], b, rank2);

    if (rank1[0] < rank2[0]) {
      return 0;
    }

    if (rank1[0] == rank2[0]) {
      if (rank1[1] <= rank2[1]) {
        return 0;
      }
    }
  }

  return 1;
}
