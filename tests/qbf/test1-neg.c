
#include "synth.h"

int check(solution_t *sol, word_t args[NARGS]) {
  word_t res[NRES];
  word_t eargs[NARGS];
  int i;
  int ret = 0;

  word_t x1 = args[0];

  for (i = 0; i < NARGS; i++) {
    eargs[i] = 0;
  }
  eargs[0] = x1;
  exec(&sol->progs[0], eargs, res);
  word_t x2 = res[0];
  if (!x2) ret += 1;

  return ret;
}
