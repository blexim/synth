#include "synth.h"

extern void prefix(word_t args[NARGS]);
extern int guard(word_t args[NARGS]);
extern void body(word_t args[NARGS]);
extern int assertion(word_t args[NARGS]);

word_t rank(prog_t *prog, word_t args[NARGS]) {
  word_t res;

  exec(prog, args, &res);

  return res;
}

int check(solution_t *solution, word_t args[NARGS]) {
  word_t vars[NARGS];
  prog_t *prog = &solution->progs[0];
  int i;

  for (i = 0; i < NARGS; i++) {
    vars[i] = args[i];
  }

  if (guard(vars)) {
    word_t r1 = rank(prog, vars);

    if (r1 <= 0) {
      return 0;
    }

    body(vars);

    word_t r2 = rank(prog, vars);

    if (r1 <= r2) {
      return 0;
    }
  }

  return 1;
}

