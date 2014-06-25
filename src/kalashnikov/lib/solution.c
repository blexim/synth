#include <stdio.h>

#include "synth.h"

void print_solution(solution_t *solution) {
  int i, j;

  for (j = 0; j < NPROGS; j++) {
    prog_t *prog = &solution->progs[j];
    printf("ops={");

    for (i = 0; i < prog->len; i++) {
      if (i != 0) {
        printf(", ");
      }

      printf("%d", prog->ops[i]);
    }

    printf("}\n");

    printf("params={");

    for (i = 0; i < (prog->len * 3); i++) {
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

  printf("evars={");

  for (i = 0; i < NEVARS; i++) {
    if (i != 0) {
      printf(", ");
    }

    printf("%d", solution->evars[i]);
  }

  printf("}\n");
}
