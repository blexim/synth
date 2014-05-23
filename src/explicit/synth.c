#include <stdio.h>

#ifndef SEARCH
 #define SEARCH
#endif

#include "synth.h"
#include "exec.h"

#define WORDMASK ((1 << WIDTH) - 1)
#define PMASK ((1 << PWIDTH) - 1)
#define OPMASK ((1 << OPLEN) - 1)

//#define DEBUG

// Generate the lexicographically next highest program.
//
// Return 0 if the new program is all 0's (i.e. we have
// wrapped around), otherwise return 1.
int next_solution(solution_t *solution) {
  prog_t *prog = &solution->prog;
  int i;

  for (i = 0; i < NEVARS; i++) {
    solution->evars[i]++;
    solution->evars[i] &= WORDMASK;

    if (solution->evars[i] != 0) {
      return 1;
    }
  }

  for (i = 0; i < CONSTS; i++) {
    prog->consts[i]++;
    prog->consts[i] &= WORDMASK;

    if (prog->consts[i] != 0) {
      return 1;
    }
  }

  for (i = 0; i < SZ*3; i++) {
    prog->params[i]++;
    prog->params[i] &= PMASK;

    if (prog->params[i] != 0) {
      return 1;
    }
  }

  for (i = 0; i < SZ; i++) {
    prog->ops[i]++;
    prog->ops[i] &= OPMASK;

    if (prog->ops[i] != 0) {
      return 1;
    }
  }

  return 0;
}

void init_solution(solution_t *solution) {
  prog_t *prog = &solution->prog;
  int i;

  for (i = 0; i < CONSTS; i++) {
    prog->consts[i] = 0;
  }

  for (i = 0; i < SZ; i++) {
    prog->ops[i] = 0;
  }

  for (i = 0; i < SZ*3; i++) {
    prog->params[i] = 0;
  }

  for (i = 0; i < NEVARS; i++) {
    solution->evars[i] = 0;
  }
}

void print_solution(solution_t *solution) {
  prog_t *prog = &solution->prog;
  int i;

  printf("ops={");

  for (i = 0; i < SZ; i++) {
    if (i != 0) {
      printf(", ");
    }

    printf("%d", prog->ops[i]);
  }

  printf("}\n");

  printf("params={");

  for (i = 0; i < SZ*3; i++) {
    if (i != 0) {
      printf(", ");
    }

    printf("%d", prog->params[i]);
  }

  printf("}\n");

  printf("consts={");

  for (i = 0; i < CONSTS; i++) {
    if (i != 0) {
      printf(", ");
    }

    printf("%d", prog->consts[i]);
  }

  printf("}\n");

  printf("evars={");

  for (i = 0; i < NEVARS; i++) {
    if (i != 0) {
      printf(", ");
    }

    printf("%d", solution->evars[i]);
  }

  printf("}\n");
}

int ok;
int print = 0;

void test(solution_t *solution, word_t args[NARGS]) {
  prog_t *prog = &solution->prog;

  if (print) {
    int i;
    int x;

    word_t res[NRES];

    exec(prog, args, res);

    for (i = 0; i < NARGS; i++) {
      x = args[i] & WORDMASK;
      printf("%d ", x);
    }

    printf("-> ");

    for (i = 0; i < NRES; i++) {
      x = res[i] & WORDMASK;
      printf("%d ", x);
    }

    printf("\n");
  }

  int valid = check(solution, args);

  if (!execok) {
    ok = 0;
    return;
  }

  if (!valid) {
    ok = 0;
  }
}

int main(void) {
  solution_t solution;
  prog_t *prog = &solution.prog;

  init_solution(&solution);

  do {
    if (!wellformed(prog) || exclude(prog)) {
      continue;
    }

    ok = 1;
    tests(&solution);

    if (ok) {
#ifdef DEBUG
      print = 1;
      tests(&solution);
#endif

      print_solution(&solution);
      return 10;
    }
  } while (next_solution(&solution));

  return 0;
}
