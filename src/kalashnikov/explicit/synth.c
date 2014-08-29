#include <stdio.h>

#ifndef SEARCH
 #define SEARCH
#endif

#include "synth.h"
#include "exec.h"
#include "solution.h"

#define WORDMASK ((1 << WIDTH) - 1)
#define PMASK ((1 << PWIDTH) - 1)
#define OPMASK ((1 << OPLEN) - 1)

//#define DEBUG

// Generate the lexicographically next highest program.
//
// Return 0 if the new program is all 0's (i.e. we have
// wrapped around), otherwise return 1.
int next_solution(solution_t *solution) {
  int i, j;

  for (i = 0; i < NEVARS; i++) {
    solution->evars[i]++;
    solution->evars[i] &= WORDMASK;

    if (solution->evars[i] != 0) {
      return 1;
    }
  }

  for (j = 0; j < NPROGS; j++) {
    prog_t *prog = &solution->progs[j];

    for (i = 0; i < CONSTS; i++) {
      prog->consts[i]++;
      prog->consts[i] &= WORDMASK;

      if (prog->consts[i] != 0) {
        return 1;
      }
    }

    for (i = 0; i < (prog->len * 3); i++) {
      prog->params[i]++;
      prog->params[i] &= PMASK;

      if (prog->params[i] != 0) {
        return 1;
      }
    }

    for (i = 0; i < prog->len; i++) {
      prog->ops[i]++;
      prog->ops[i] &= OPMASK;

      if (prog->ops[i] != 0) {
        return 1;
      }
    }
  }

  return 0;
}

void init_solution(solution_t *solution) {
  int i, j;

  for (j = 0; j < NPROGS; j++) {
    prog_t *prog = &solution->progs[j];
    prog->len = SZ;

    for (i = 0; i < CONSTS; i++) {
      prog->consts[i] = 0;
    }

    for (i = 0; i < SZ; i++) {
      prog->ops[i] = 0;
    }

    for (i = 0; i < SZ*3; i++) {
      prog->params[i] = 0;
    }
  }

  for (i = 0; i < NEVARS; i++) {
    solution->evars[i] = 0;
  }
}

int ok;
int print = 0;

void test(solution_t *solution, word_t args[NARGS]) {
#if 0
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
#endif

  int score = check(solution, args);

  if (!execok) {
    return;
  }

  if (score != MAXFIT) {
    ok = 0;
  }
}

int main(void) {
  solution_t solution;
  int i;

  init_solution(&solution);

  do {
    int progok = 1;

    for (i = 0; i < NPROGS; i++) {
      prog_t *prog = &solution.progs[i];

      if (!wellformed(prog) || exclude(prog)) {
        progok = 0;
        break;
      }
    }

    if (!progok) {
      continue;
    }

    ok = 1;
    execok = 1;
    tests(&solution);

    if (ok && execok) {
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
