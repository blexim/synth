#include "synth.h"

extern int prefix(word_t in_vars[NARGS], word_t out_vars[NARGS]);
extern int guard(word_t in_vars[NARGS]);
extern void body(word_t in_vars[NARGS], word_t out_vars[NARGS]);
extern int assertion(word_t args[NARGS]);

int inv(prog_t *prog, word_t args[NARGS]) {
  word_t res[NRES];
  int i;

  for (i = 0; i < NONDET_ARGS; i++) {
    args[i] = 0;
  }

  exec(prog, args, res);

  return res[0];
}

int skolem(prog_t *prog, word_t pre_vars[NARGS]) {
  word_t res[NRES];
  int i;

  for (i = 0; i < NONDET_ARGS; i++) {
    pre_vars[i] = 0;
  }

  exec(prog, pre_vars, res);

  for (i = 0; i < NONDET_ARGS; i++) {
    pre_vars[i] = res[i];
  }

  return 0;
}


void rank(prog_t *prog, word_t args[NARGS], word_t res[NRES]) {
  exec(prog, args, res);
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
  word_t pre_vars[NARGS], post_vars[NARGS];
  prog_t *inv_prog = &solution->progs[0];
  prog_t *skolem_prog = &solution->progs[1];
  prog_t *rank_prog = &solution->progs[2];
  int i;

  for (i = 0; i < NARGS; i++) {
    pre_vars[i] = solution->evars[i];
  }

  if (!prefix(pre_vars, post_vars)) {
    return 0;
  }

  if (!inv(inv_prog, post_vars)) {
    return 0;
  }

  for (i = 0; i < NARGS; i++) {
    pre_vars[i] = args[i];
  }

  if (inv(inv_prog, pre_vars) && guard(pre_vars)) {
    word_t r1[NRES], r2[NRES];

    rank(rank_prog, pre_vars, r1);
    
    skolem(skolem_prog, pre_vars);
    body(pre_vars, post_vars);

    rank(rank_prog, post_vars, r2);

    if (!nonzero(r1)) {
      return 0;
    }

    if (cmp(r1, r2) <= 0) {
      return 0;
    }

    if (!inv(inv_prog, post_vars)) {
      return 0;
    }
  }

  for (i = 0; i < NARGS; i++) {
    pre_vars[i] = args[i];
  }

  if (inv(inv_prog, pre_vars) && !guard(pre_vars)) {
    if (assertion(pre_vars)) {
      return 0;
    }
  }

  return 1;
}
