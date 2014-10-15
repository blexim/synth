#include <stdio.h>

#ifndef SEARCH
 #define SEARCH
#endif

#include "synth.h"
#include "exec.h"
#include "io.h"

#define PMASK ((1 << PWIDTH) - 1)
#define OPMASK ((1 << OPLEN) - 1)

word_t init_vector[NARGS];

// Generate the lexicographically next highest program.
//
// Return 0 if the new program is all 0's (i.e. we have
// wrapped around), otherwise return 1.
int next_input(word_t args[NARGS]) {
  int i;

  for (i = 0; i < NARGS; i++) {
    args[i]++;
    args[i] &= WORDMASK;

    if (args[i] != 0) {
      return 1;
    }
  }

  return 0;
}

int reached_init(word_t args[NARGS]) {
  int i;

  for (i = 0; i < NARGS; i++) {
    if (args[i] != init_vector[i]) {
      return 0;
    }
  }

  return 1;
}

void init_args(word_t args[NARGS]) {
  int i;

  for (i = 0; i < NARGS; i++) {
    args[i] = init_vector[i];
  }
}

void print_args(word_t args[NARGS]) {
  int i;

  printf("cex_args={");

  for (i = 0; i < NARGS; i++) {
    if (i != 0) {
      printf(", ");
    }

    printf("%d", args[i]);
  }

  printf("}\n");
}

void load_init_vector() {
  int i;

  load_tests();

  for (i = 0; i < NARGS; i++) {
    init_vector[i] = 0;
  }

  if (numtests > 0) {
    for (i = 0; i < NARGS; i++) {
      init_vector[i] = test_vectors[numtests - 1][i];
    }
  }
}

int main(void) {
  word_t args[NARGS];
  int i;

  for (i = 0; i < NARGS; i++) {
    init_vector[i] = 0;
  }

  load_solution(&solution);
  //load_init_vector();
  init_args(args);

  do {
    execok = 1;

    if (check(&solution, args) != MAXFIT || !execok) {
      print_args(args);
      return 10;
    }

    next_input(args);
  } while (!reached_init(args));

  return 0;
}
