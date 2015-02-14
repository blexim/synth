#include "synth.h"

extern void prefix(word_t args[NARGS], word_t out_args[NARGS]);
extern int guard(word_t args[NARGS]);
extern void body(word_t args[NARGS], word_t out_args[NARGS]);
extern int assertion(word_t args[NARGS]);

int inv(prog_t *prog, word_t args[NARGS]) {
  word_t res[NRES];

  exec(prog, args, res);

  return res[0];
}

int check(solution_t *solution, word_t args[NARGS]) {
  word_t vars[NARGS], post_vars[NARGS];
  prog_t *prog = &solution->progs[0];
  int i;

  for (i = 0; i < NARGS; i++) {
    vars[i] = solution->evars[i];
  }

  prefix(vars, post_vars);

  if (!inv(prog, post_vars)) {
    return 0;
  }

  for (i = 0; i < NARGS; i++) {
    vars[i] = args[i];
  }

  if (guard(vars) && inv(prog, vars)) {
    body(vars, post_vars);

    if (!inv(prog, post_vars)) {
      return 0;
    }
  }

  for (i = 0; i < NARGS; i++) {
    vars[i] = args[i];
  }

  if (!guard(vars) && inv(prog, vars)) {
    if (assertion(vars)) {
      return 0;
    }
  }

  return 1;
}

