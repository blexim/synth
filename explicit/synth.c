#include <stdio.h>

#ifndef SEARCH
 #define SEARCH
#endif

#include "synth.h"
#include "exec.h"

#define WORDMASK ((1 << WIDTH) - 1)
#define PMASK ((1 << PWIDTH) - 1)
#define OPMASK ((1 << OPLEN) - 1)

extern int execok;

// Generate the lexicographically next highest program.
//
// Return 0 if the new program is all 0's (i.e. we have
// wrapped around), otherwise return 1.
int next_prog(prog_t *prog) {
  int i;

  for (i = 0; i < CONSTS; i++) {
    prog->consts[i]++;
    prog->consts[i] &= WORDMASK;

    if (prog->consts[i] != 0) {
      return 1;
    }
  }

  for (i = 0; i < SZ*2; i++) {
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

void init_prog(prog_t *prog) {
  int i;

  for (i = 0; i < CONSTS; i++) {
    prog->consts[i] = 0;
  }

  for (i = 0; i < SZ; i++) {
    prog->ops[i] = 0;
  }

  for (i = 0; i < SZ*2; i++) {
    prog->params[i] = 0;
  }
}

void print_prog(prog_t *prog) {
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

  for (i = 0; i < SZ*2; i++) {
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
}

int ok;

void test(prog_t *prog, word_t args[NARGS]) {
  int i;
  word_t res[NRES];

  exec(prog, args, res);

  for (i = 0; i < NRES; i++) {
    res[i] &= WORDMASK;
  }

  if (!execok) {
    ok = 0;
    return;
  }

  int valid = check(args, res);

  if (!valid) {
    ok = 0;
  }
}

int main(void) {
  prog_t prog;

  init_prog(&prog);

  do {
    if (exclude(&prog)) {
      continue;
    }

    ok = 1;
    tests(&prog);

    if (ok) {
      print_prog(&prog);
      return 10;
    }
  } while (next_prog(&prog));

  return 0;
}
