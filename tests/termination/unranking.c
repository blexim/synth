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

int check(solution_t *solution, word_t args[NARGS]) {
  word_t pre_vars[NARGS], post_vars[NARGS];
  prog_t *inv_prog = &solution->progs[0];
  prog_t *skolem_prog = &solution->progs[1];
  int i;

  for (i = 0; i < NARGS; i++) {
    pre_vars[i] = solution->evars[i];
  }

  if (!prefix(pre_vars, post_vars)) {
    return 0;
  }

  if (!inv(inv_prog, post_vars) || !guard(post_vars)) {
    return 0;
  }

  for (i = 0; i < NARGS; i++) {
    pre_vars[i] = args[i];
  }

  if (inv(inv_prog, pre_vars) && guard(pre_vars)) {
    skolem(skolem_prog, pre_vars);

    body(pre_vars, post_vars);

    if (!inv(inv_prog, post_vars)) {
      return 0;
    }

    if (!guard(post_vars)) {
      return 0;
    }
  }

  return 1;
}
