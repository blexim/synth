#include "synth.h"

extern int prefix(word_t in_vars[NARGS], word_t out_vars[NARGS]);
extern int guard(word_t in_vars[NARGS]);
extern void body(word_t in_vars[NARGS], word_t out_vars[NARGS]);
extern int assertion(word_t args[NARGS]);

#define COND

int inv(prog_t *prog, word_t args[NARGS]) {
#ifndef COND
  return 1;
#else
  word_t res[NRES];

  exec(prog, args, res);

  return res[0];
#endif
}

void rank(prog_t *prog, word_t args[NARGS], word_t res[NRES]) {
  exec(prog, args, res);
}

int cmp(word_t rank1[NRES], word_t rank2[NRES]) {
  int i;

#ifdef COND
  i = 1;
#else
  i = 0;
#endif

  while (i < NRES) {
    if (rank1[i] < rank2[i]) {
      return -1;
    } else if (rank1[i] > rank2[i]) {
      return 1;
    }

    i++;
  }

  return 0;
}

int nonzero(word_t rank[NRES]) {
  int i;

#ifdef COND
  i = 1;
#else
  i = 0;
#endif

  while (i < NRES) {
    if (rank[i] > 0) {
      return 1;
    }

    i++;
  }

  return 0;
}

int check(solution_t *solution, word_t args[NARGS]) {
  word_t pre_vars[NARGS], post_vars[NARGS];
  prog_t *prog = &solution->progs[0];
  int i;

  for (i = 0; i < NARGS; i++) {
    pre_vars[i] = args[i];
  }

  if (prefix(pre_vars, post_vars)) {
    if (!inv(prog, post_vars)) {
      return 0;
    }
  }

  for (i = 0; i < NARGS; i++) {
    pre_vars[i] = args[i];
  }

  if (guard(pre_vars) && inv(prog, pre_vars)) {
    word_t r1[NRES];
    word_t r2[NRES];

    rank(prog, pre_vars, r1);

    if (!nonzero(r1)) {
      return 0;
    }

    body(pre_vars, post_vars);

    rank(prog, post_vars, r2);

    if (cmp(r1, r2) <= 0) {
      return 0;
    }

    if (!inv(prog, post_vars)) {
      return 0;
    }
  }

  return 1;
}

