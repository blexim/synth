#include <stdio.h>

#ifndef SEARCH
 #define SEARCH
#endif

#include "synth.h"
#include "exec.h"

extern int execok;

#define WORDMASK ((1 << WIDTH) - 1)
#define PMASK ((1 << PWIDTH) - 1)
#define OPMASK ((1 << OPLEN) - 1)

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

void init_args(word_t args[NARGS]) {
  int i;

  for (i = 0; i < NARGS; i++) {
    args[i] = 0;
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

int main(void) {
  word_t args[NARGS];
  int i;

  init_args(args);

  do {
    execok = 1;

    if (!check(&prog, args) || !execok) {
      print_args(args);
      return 10;
    }
  } while (next_input(args));

  return 0;
}
