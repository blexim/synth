#include "synth.h"

extern int prefix(word_t args[NARGS]);
extern int guard(word_t args[NARGS]);
extern int body(word_t args[NARGS]);
extern int assertion(word_t args[NARGS]);

int inv(prog_t *prog, word_t args[NARGS]) {
  word_t res[NRES];

  exec(prog, args, res);

  return res[0];
}

int check(solution_t *solution, word_t args[NARGS]) {
  word_t vars[NARGS];
  prog_t *prog = &solution->progs[0];
  int i;

  for (i = 0; i < NARGS; i++) {
    vars[i] = args[i];
  }

  if (prefix(vars) && !inv(prog, vars)) {
    return 0;
  }

  for (i = 0; i < NARGS; i++) {
    vars[i] = args[i];
  }

  if (guard(vars) && inv(prog, vars)) {
    if (!body(vars)) {
      return 0;
    }

    if (!inv(prog, vars)) {
      return 0;
    }
  }

  for (i = 0; i < NARGS; i++) {
    vars[i] = args[i];
  }

  if (!guard(vars) && inv(prog, vars)) {
    if (!assertion(vars)) {
      return 0;
    }
  }

  return 1;
}

