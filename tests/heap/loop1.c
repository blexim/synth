#include "synth.h"
#include "heaplib.h"

int inv(solution_t *sol, word_t args[NARGS]) {
  word_t res[NRES];

  exec(&sol->progs[0], args, res);

  return res[0];
}

int check(solution_t *sol, word_t args[NARGS]) {
  word_t res[NRES];

  for (int i = 0; i < NARGS; i++) {
    if (!is_ptr(args[i])) {
      return 1;
    }
  }

  word_t x = args[0];
  word_t y = args[1];

  if (path(1, 2, args)) {
    if (!inv(sol, args)) {
      return 0;
    }
  }

  if (inv(sol, args) && x != y) {
    if (x == 0) {
      return 0;
    }

    x = deref(x, args);
    word_t args2[NARGS];

    args2[0] = x;

    for (int i = 1; i < NARGS; i++) {
      args2[i] = args[i];
    }

    if (!inv(sol, args2)) {
      return 0;
    }
  }

  return 1;
}
