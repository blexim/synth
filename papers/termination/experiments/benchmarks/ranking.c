#include "synth.h"

extern int prefix(word_t in_vars[NARGS], word_t out_vars[NARGS]);
extern int guard(word_t in_vars[NARGS]);
extern void body(word_t in_vars[NARGS], word_t out_vars[NARGS]);
extern int assertion(word_t args[NARGS]);

word_t rank(prog_t *prog, word_t args[NARGS]) {
  word_t res;

  exec(prog, args, &res);

  return res;
}

int check(solution_t *solution, word_t args[NARGS]) {
  word_t pre_vars[NARGS], post_vars[NARGS];
  prog_t *prog = &solution->progs[0];
  int i;

  for (i = 0; i < NARGS; i++) {
    pre_vars[i] = args[i];
  }

  if (guard(pre_vars)) {
    word_t r1 = rank(prog, pre_vars);

    if (r1 <= 0) {
      return 0;
    }

    body(pre_vars, post_vars);

    word_t r2 = rank(prog, post_vars);

    if (r1 <= r2) {
      return 0;
    }
  }

  return 1;
}

