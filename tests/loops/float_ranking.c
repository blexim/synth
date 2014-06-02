#include "synth.h"

#include <math.h>

extern int prefix(word_t args[NARGS]);
extern int guard(word_t args[NARGS]);
extern void body(word_t args[NARGS]);
extern int assertion(word_t args[NARGS]);

fword_t rank(prog_t *prog, word_t args[NARGS]) {
  word_t res[2];

  exec(prog, args, res);

  fi_t fi;
  fi.x = res[0];
  return fi.f;
}

word_t inv(prog_t *prog, word_t args[NARGS]) {
  word_t res[2];

  exec(prog, args, res);

  return res[1];
}

int check(solution_t *solution, word_t args[NARGS]) {
  word_t vars[NARGS];
  prog_t *prog = &solution->progs[0];
  int i;

  for (i = 0; i < NARGS; i++) {
    vars[i] = args[i];
  }

  if(prefix(vars) && !inv(prog, vars)) {
    return 0;
  }

  for (i = 0; i < NARGS; i++) {
    vars[i] = args[i];
  }

  if (inv(prog, vars) && guard(vars)) {
    fword_t r1 = rank(prog, vars);

    if(!isnormal(r1)) {
      return 0;
    }

    if (r1 <= 0.0) {
      return 0;
    }

    body(vars);

    fword_t r2 = rank(prog, vars);

    if (!isnormal(r2)) {
      return 0;
    }

    if (r1 <= r2) {
      return 0;
    }

    if (!inv(prog, vars)) {
      return 0;
    }
  }

  return 1;
}

