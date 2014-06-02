#include "synth.h"

#define WORDMASK ((1 << WIDTH) - 1)

int check(solution_t *solution, word_t args[2]) {
  word_t a[2], b[2];
  word_t rank1[2], rank2[2];
  int q, y, q_, y_;

  q = args[0];
  y = args[1];

  if (q >= 0) {
      q_ = q - y;
      y_ = y + 1;
  }

  a[0] = q;
  a[1] = y;
  exec(&solution->progs[0], a, rank1);

  if (rank1[0] == 0 || rank1[1] == 0) {
    return 0;
  }

  b[0] = q_;
  b[1] = y_;
  exec(&solution->progs[0], b, rank2);

  if (rank1[0] < rank2[0]) {
    return 0;
  }

  if (rank1[0] == rank2[0]) {
    if (rank1[1] <= rank2[1]) {
      return 0;
    }
  }

  return 1;
}
