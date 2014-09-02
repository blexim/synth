#include "synth.h"

extern int prefix(word_t in_vars[NARGS], word_t out_vars[NARGS]);
extern int guard(word_t in_vars[NARGS]);
extern void body(word_t in_vars[NARGS], word_t out_vars[NARGS]);
extern int assertion(word_t args[NARGS]);

#define COND

int recurrence(solution_t *solution, word_t args[NARGS]) {
  word_t res[NRES];

  exec(&solution->progs[0], args, res);

  return res[0];
}

int inv(solution_t *solution, word_t args[NARGS]) {
#ifndef COND
  return 1;
#else
  word_t res[NRES];

  exec(&solution->progs[1], args, res);

  return res[0];
#endif
}

void rank_function(solution_t *solution, word_t args[NARGS], word_t res[NRES]) {
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
    if (rank[i] != 0) {
      return 1;
    }
  }

  return 0;
}

int check_rank(solution_t *solution, word_t args[NARGS]) {
  word_t pre_vars[NARGS], post_vars[NARGS];
  int i;

  for (i = 0; i < NARGS; i++) {
    pre_vars[i] = args[i];
    post_vars[i] = 0;
  }

  if (prefix(pre_vars, post_vars)) {
    if (!inv(solution, post_vars)) {
      return 0;
    }
  }

  for (i = 0; i < NARGS; i++) {
    pre_vars[i] = args[i];
    post_vars[i] = 0;
  }

  if (guard(pre_vars) && inv(solution, pre_vars)) {
    word_t r1[NRES];
    word_t r2[NRES];

    rank_function(solution, pre_vars, r1);

    if (!nonzero(r1)) {
      return 0;
    }

    body(pre_vars, post_vars);

    rank_function(solution, post_vars, r2);

    if (cmp(r1, r2) <= 0) {
      return 0;
    }

    if (!inv(solution, post_vars)) {
      return 0;
    }
  }

  return 1;
}


int check_recurrence(solution_t *solution, word_t args[NARGS]) {
  word_t pre_vars[NARGS], post_vars[NARGS];
  int i;

  for (i = 0; i < NARGS; i++) {
    pre_vars[i] = solution->evars[i];
    post_vars[i] = 0;
  }

  if (!prefix(pre_vars, post_vars)) {
    return 0;
  }

  if (!recurrence(solution, post_vars) || !guard(post_vars)) {
    return 0;
  }

  for (i = 0; i < NARGS; i++) {
    pre_vars[i] = args[i];
    post_vars[i] = 0;
  }

  if (guard(pre_vars) && recurrence(solution, pre_vars)) {
    body(pre_vars, post_vars);

    if (!recurrence(solution, post_vars)) {
      return 0;
    }

    if (!guard(post_vars)) {
      return 0;
    }
  }

  return 1;
}

int check(solution_t *solution, word_t args[NARGS]) {
  word_t rank_args[NARGS];
  word_t recurrence_args[NARGS];
  int i;

  for (i = 0; i < NARGS/2; i++) {
    rank_args[i] = args[i];
    recurrence_args[i] = args[i + (NARGS/2)];
  }

  for (i = NARGS/2; i < NARGS; i++) {
    rank_args[i] = 0;
    recurrence_args[i] = 0;
  }

  if (check_rank(solution, rank_args)) {
    return 1;
  }

  if (check_recurrence(solution, recurrence_args)) {
    return 1;
  }

  return 0;
}
