/*
 * This example illustrates a massive ballache:
 * we can encode arithmetic properties using just
 * pointer equality and loops.
 */

#include "synth.h"
#include "heaptheory.h"

int inv(prog_t *prog, word_t args[NARGS]) {
  word_t res[NRES];

  exec(prog, args, res);

  return res[0];
}

int check(solution_t *solution, word_t args[NARGS]) {
  word_t a = 0;
  word_t b = 1;
  word_t c = 2;
  word_t d = 3;
  word_t two = 4;
  word_t nil = 5;

  word_t state1[NARGS];
  word_t state2[NARGS];

  int i;

  prog_t *I1 = &solution->progs[0];
  prog_t *I2 = &solution->progs[1];
  prog_t *I3 = &solution->progs[2];

  for (i = 0; i < NHEAP; i++) {
    args[idx(nil, i)] = INF;
    args[idx(i, i)] = 0;
  }

  // I1 is initial
  if (alias(args, a, nil)) {
    if (!inv(I1, args)) {
      return 0;
    }
  }

  // I1 is inductive
  if (inv(I1, args)) {
    alloc(args, state2, b);
    update(state2, state1, b, a);
    assign(state1, state2, a, b);

    if (path(state2, a, nil)) {
      if (!inv(I1, state2)) {
        return 0;
      }
    }
  }

  // I1 ==> I2 is initial
  if (inv(I1, args)) {
    assign(args, state1, c, a);
    assign(state1, state2, b, a);

    if (!inv(I2, state2)) {
      return 0;
    }
  }

  // I2 is inductive
  if (!alias(args, c, nil) && inv(I2, args)) {
    alloc(args, state1, d);
    update(state1, state2, b, d);
    assign(state2, state1, b, d);
    lookup(state1, state2, c, c);

    if (!inv(I2, state2)) {
      return 0;
    }
  }

  // I2 ==> I3
  if (inv(I2, args) && alias(args, c, nil)) {
    alloc(args, state1, two);
    alloc(state1, state2, a);
    update(state2, state1, a, nil);
    update(state1, state2, two, a);
    assign(state2, state1, d, nil);

    if (!inv(I3, state1)) {
      return 0;
    }
  }

  // I3 is inductive
  if (inv(I3, args) && !alias(args, b, nil)) {
    if (alias(args, d, nil)) {
      assign(args, state1, d, two);
    } else {
      for (i = 0; i < NARGS; i++) {
        state1[i] = args[i];
      }
    }

    lookup(state1, state2, b, b);
    lookup(state2, state1, d, d);

    if (!inv(I3, state1)) {
      return 0;
    }
  }

  // I3 && !guard ==> assertion
  if (inv(I3, args) && alias(args, b, nil)) {
    if (alias(args, d, nil)) {
      return 0;
    }
  }

  return 1;
}
