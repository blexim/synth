#include "synth.h"

//#define SIMPLE

int inv(prog_t *prog, word_t q, word_t x) {
  word_t args[2];
  word_t ret[NRES];

  args[0] = x;
  args[1] = q;

  exec(prog, args, ret);

  return ret[0];
}

int check(solution_t *sol, word_t args[2]) {
  word_t x0 = sol->evars[0];
  word_t q0 = sol->evars[1];

  word_t x;
  word_t q;

  prog_t *prog = &sol->progs[0];

#ifdef SIMPLE
  if (q0 <= 0) {
    return 0;
  }

  if (!inv(prog, q0, x0)) {
    return 0;
  }
#else
  q = q - x;
  x = x + 1;

  if (q <= 0) {
    return 0;
  }

  if (!inv(prog, q, x)) {
    return 0;
  }
#endif

  x = args[0];
  q = args[1];

  if (inv(prog, q, x) && q > 0 
#ifndef SIMPLE
      && (x != x0 || q != q0)
#endif
      ) {
    q = q - x;
    x = x + 1;

    if (!inv(prog, q, x)) {
      return 0;
    }

    if (q <= 0) {
      return 0;
    }
  }

#ifndef SIMPLE
  x = args[0];
  q = args[1];

  if (inv(prog, q, x) && q <= 0) {
    if (x != x0 || q != q0) {
      return 0;
    }
  }
#endif

  return 1;
}
