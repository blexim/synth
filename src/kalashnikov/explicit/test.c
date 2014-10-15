#include <stdio.h>

#ifndef SEARCH
 #define SEARCH
#endif

#include "synth.h"
#include "exec.h"
#include "solution.h"
#include "io.h"

#define WORDMASK ((1 << WIDTH) - 1)
#define PMASK ((1 << PWIDTH) - 1)
#define OPMASK ((1 << OPLEN) - 1)

//#define DEBUG

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

  load_solution(&solution);
  load_tests();

  ok = 1;
  execok = 1;

  for (i = 0; i < numtests; i++) {
    printf("Test %d: ", i);
    if (check(&solution, test_vectors[i])) {
      printf("OK\n");
    } else {
      printf("BAD\n");
    }
  }

  if (ok && execok) {
#ifdef DEBUG
    print = 1;
    tests(&solution);
#endif
  }

  return 0;
}
