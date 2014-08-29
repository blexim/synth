
#include "synth.h"

int check(solution_t *sol, word_t args[NARGS]) {
  word_t res[NRES];
  word_t eargs[NARGS];
  int i;
  int ret = 0;
  word_t x1 = sol->evars[0];
  word_t x2 = sol->evars[1];
  word_t x3 = sol->evars[2];
  word_t x4 = args[0];

  for (i = 0; i < NARGS; i++) {
    eargs[i] = 0;
  }
  eargs[0] = x4;
  exec(&sol->progs[0], eargs, res);
  word_t x5 = res[0];
  exec(&sol->progs[1], eargs, res);
  word_t x6 = res[0];
  exec(&sol->progs[2], eargs, res);
  word_t x7 = res[0];
  word_t x8 = args[1];

  for (i = 0; i < NARGS; i++) {
    eargs[i] = 0;
  }
  eargs[0] = x4;
  eargs[1] = x8;
  exec(&sol->progs[3], eargs, res);
  word_t x9 = res[0];
  exec(&sol->progs[4], eargs, res);
  word_t x10 = res[0];
  if (x1) ret += 1;
  if (x4 || x5 || !x1) ret += 1;
  if (x4 || x1 || !x5) ret += 1;
  if (x4 || x6 || !x3) ret += 1;
  if (x4 || x3 || !x6) ret += 1;
  if (x5 || !x4 || !x3) ret += 1;
  if (x3 || !x4 || !x5) ret += 1;
  if (x6 || !x4 || !x2) ret += 1;
  if (x2 || !x4 || !x6) ret += 1;
  if (x9 || !x8 || !x5) ret += 1;
  if (x5 || !x8 || !x9) ret += 1;
  if (x10 || !x8 || !x7) ret += 1;
  if (x7 || !x8 || !x10) ret += 1;
  if (x8 || x9 || !x7) ret += 1;
  if (x8 || x7 || !x9) ret += 1;
  if (x8 || x10 || !x6) ret += 1;
  if (x8 || x6 || !x10) ret += 1;
  if (x10 || !x9) ret += 1;

  return ret;
}
