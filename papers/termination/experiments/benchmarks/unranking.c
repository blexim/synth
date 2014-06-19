#include "synth.h"

extern int prefix(word_t in_vars[NARGS], word_t out_vars[NARGS]);
extern int guard(word_t in_vars[NARGS]);
extern void body(word_t in_vars[NARGS], word_t out_vars[NARGS]);
extern int assertion(word_t args[NARGS]);

int inv(prog_t *prog, word_t args[NARGS]) {
  word_t res[NRES];

  exec(prog, args, res);

  return res[0];
}

int check(solution_t *solution, word_t args[NARGS]) {
  word_t pre_vars[NARGS], post_vars[NARGS];
  prog_t *prog = &solution->progs[0];
  int i;

  for (i = 0; i < NARGS; i++) {
    pre_vars[i] = solution->evars[i];
  }

  if (!prefix(pre_vars, post_vars)) {
    return 0;
  }

  if (!inv(prog, post_vars) || !guard(post_vars)) {
    return 0;
  }

  for (i = 0; i < NARGS; i++) {
    pre_vars[i] = args[i];
  }

  if (guard(pre_vars) && inv(prog, pre_vars)) {
    body(pre_vars, post_vars);

    if (!inv(prog, post_vars)) {
      return 0;
    }

    if (!guard(post_vars)) {
      return 0;
    }
  }

  return 1;
}
