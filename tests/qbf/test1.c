
#include "synth.h"

int check(solution_t *sol, word_t args[NARGS]) {
  word_t res[NRES];
  word_t eargs[NARGS];
  int i;
  int ret = 0;

  word_t x1 = sol->evars[0];
  word_t x2 = args[0];
  if (x2) ret += 1;

  return ret;
}
