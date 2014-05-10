#include "synth.h"

int check(prog_t *prog, word_t args[2]) {
  word_t res[1];
  exec(prog, args, res);

  word_t y = args[0];
  word_t r = res[0];

  int a=1, b=0, z=1, c=0;

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
        z=y << 3; a=!a; b=!b; } } }

#ifdef SEARCH
  y &= ((1 << WIDTH) -1);
#endif

  return y == r;
}
