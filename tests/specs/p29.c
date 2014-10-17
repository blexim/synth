#include "synth.h"

int check(solution_t *solution, word_t args[2]) {
  word_t res[NRES];
  exec(&solution->progs[0], args, res);

  word_t y = args[0];
  word_t r = res[0];

  word_t a=1, b=0, z=1, c=0;

  while(1) {
    if (a == 0) {
      if (b == 0) {
        y=z+y; a =!a; b=!b;c=!c;
        if (! c) break;
      } else {
        z=z+y; a=!a; b=!b; c=!c;
        if (! c) break;
      }
    } else {
      if (b == 0) { z=y << 2; a=!a; }
      else {
        z=y << 3; a=!a; b=!b; } }
  }

#ifdef SEARCH
  y &= WORDMASK;
  r &= WORDMASK;
#endif

  return y == r;
}
