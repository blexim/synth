#include "synth.h"

extern int outer_guard(word_t in_vars[NARGS]);
extern int inner_prefix(word_t in_vars[NARGS], word_t out_vars[NARGS]);
extern int inner_suffix(word_t in_vars[NARGS], word_t out_vars[NARGS]);

extern int inner_guard(word_t in_vars[NARGS]);
extern int inner_body(word_t in_vars[NARGS], word_t out_vars[NARGS]);

#define COND

int inv(solution_t *solution, word_t args[NARGS]) {
#ifndef COND
  return 1;
#else
  word_t res[NRES];

  exec(&solution->progs[0], args, res);

  return res[0];
#endif
}

int summary(solution_t *solution, word_t args1[NARGS], word_t args2[NARGS]) {
  word_t args[NARGS];
  word_t res[NRES];
  int i;

  for (i = 0; i < NARGS/2; i++) {
    args[i] = args1[i];
    args[i + NARGS/2] = args2[i];
  }

  exec(&solution->progs[1], args, res);

  return res[0];
}

void rank(solution_t *solution, word_t args[NARGS], word_t res[NRES]) {
  exec(&solution->progs[2], args, res);
}

int cmp(word_t rank1[NRES], word_t rank2[NRES]) {
  int i;

  for (i = 0; i < NRES; i++) {
    if (rank1[i] < rank2[i]) {
      return -1;
    } else if (rank1[i] > rank2[i]) {
      return 1;
    }
  }

  return 0;
}

int nonzero(word_t rank[NRES]) {
  int i;

  for (i = 0; i < NRES; i++) {
    if (rank[i] > 0) {
      return 1;
    }
  }

  return 0;
}

int check(solution_t *solution, word_t args[NARGS]) {
  word_t x[NARGS], x_[NARGS], x__[NARGS];
  int i;

  for (i = 0; i < NARGS/2; i++) {
    x[i] = args[i];
    x_[i] = 0;
  }
  for (; i < NARGS; i++) {
    x[i] = 0;
    x_[i] = 0;
  }

  if (outer_guard(x) && inner_prefix(x, x_)) {
    if (!summary(solution, x, x_)) {
      return 0;
    }
  }

  for (i = 0; i < NARGS/2; i++) {
    x[i] = args[i];
    x_[i] = args[i + NARGS/2];
    x__[i] = 0;
  }
  for (; i < NARGS; i++) {
    x[i] = 0;
    x_[i] = 0;
    x__[i] = 0;
  }

  if (inner_guard(x_) && inner_body(x_, x__) && summary(solution, x, x_)) {
    if (!summary(solution, x, x__)) {
      return 0;
    }
  }

  for (i = 0; i < NARGS/2; i++) {
    x[i] = args[i];
    x_[i] = args[i + NARGS/2];
    x__[i] = 0;
  }
  for (; i < NARGS; i++) {
    x[i] = 0;
    x_[i] = 0;
    x__[i] = 0;
  }

  if (outer_guard(x) && !inner_guard(x_) && summary(solution, x, x_) && inner_suffix(x_, x__)) {
    word_t r1[NRES];
    word_t r2[NRES];

    rank(solution, x, r1);
    rank(solution, x__, r2);

    if (!nonzero(r1)) {
      return 0;
    }

    if (cmp(r1, r2) <= 0) {
      return 0;
    }
  }

  return 1;
}

