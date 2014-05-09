#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#ifndef SEARCH
 #define SEARCH
#endif

#include "synth.h"
#include "exec.h"

#define WORDMASK ((1 << WIDTH) - 1)
//#define WORDMASK 0xffffffff
#define PMASK ((1 << PWIDTH) - 1)
#define OPMASK ((1 << OPLEN) - 1)

#define POPSIZE 10
#define KEEP 1
#define KILL 1

#define MUTATION_PROB 0.01

#define PRINT_GEN 0

extern int execok;

int generation;

void rand_prog(prog_t *prog) {
  int i;

  for (i = 0; i < SZ; i++) {
    prog->ops[i] = rand() % (MAXOPCODE + 1);
  }

  for (i = 0; i < CONSTS; i++) {
    prog->consts[i] = rand() & WORDMASK;
  }

  for (i = 0; i < SZ*2; i++) {
    prog->params[i*2] = rand() % (i + NARGS + CONSTS);
    prog->params[i*2+1] = rand() % (i + NARGS + CONSTS);
  }
}

int should_mutate() {
  return (rand() < (RAND_MAX * MUTATION_PROB));
}

void mutate(prog_t *b) {
  int i;

  for (i = 0; i < SZ; i++) {
    if (should_mutate()) {
      b->ops[i] = rand() % (MAXOPCODE + 1);
    }
  }

  for (i = 0; i < CONSTS; i++) {
    if (should_mutate()) {
      b->consts[i] = rand() & WORDMASK;
    }
  }

  for (i = 0; i < SZ*2; i++) {
    if (should_mutate()) {
      b->params[i*2] = rand() % (i + NARGS + CONSTS);
    }

    if (should_mutate()) {
      b->params[i*2+1] = rand() % (i + NARGS + CONSTS);
    }
  }
}

#define cross(x, y, z) (z = (rand() % 2) ? x : y)

void crossover(prog_t *a, prog_t *b, prog_t *c) {
  int i;

  for (i = 0; i < SZ; i++) {
    cross(a->ops[i], b->ops[i], c->ops[i]);
  }

  for (i = 0; i < CONSTS; i++) {
    cross(a->consts[i], b->consts[i], c->consts[i]);
  }

  for (i = 0; i < SZ*2; i++) {
    cross(a->params[i*2], b->params[i*2], c->params[i*2]);
    cross(a->params[i*2+1], b->params[i*2+1], c->params[i*2+1]);
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

int fitnesses[POPSIZE];

int compare(const void *v1, const void *v2) {
  int *i1 = (int *) v1;
  int *i2 = (int *) v2;
  int f1 = fitnesses[*i1];
  int f2 = fitnesses[*i2];

  return f1 - f2;
}

void next_gen(prog_t *previous, prog_t *next) {
  int indices[POPSIZE];
  int i, j;

  for (i = 0; i < POPSIZE; i++) {
    indices[i] = i;
    fitnesses[i] = fitness(&previous[i]);
  }

  qsort(indices, POPSIZE, sizeof(int), compare);

  if (PRINT_GEN && (generation % PRINT_GEN) == 0) {
    printf("Fittest: %d, least fit: %d\n",
        fitnesses[indices[POPSIZE-1]],
        fitnesses[indices[0]]);
  }

  // Copy the fittest individuals straight into the next generation.
  j = 0;

  for (i = 0; i < KEEP; i++) {
    prog_t *p = &previous[indices[POPSIZE - i - 1]];

    memcpy(&next[j], p, sizeof(prog_t));
    j++;
  }

  // Now generate some random individuals.

  for (i = 0; i < KILL; i++) {
    rand_prog(&next[j]);
    j++;
  }

  // Finally, let the somewhat-fit individuals from the previous generation breed.

  while (j < POPSIZE) {
    int idx = KILL + (rand() % (POPSIZE - KILL));
    idx = indices[idx];
    prog_t *a = &previous[idx];

    idx = KILL + (rand() % (POPSIZE - KILL));
    idx = indices[idx];
    prog_t *b = &previous[idx];

    crossover(a, b, &next[j]);
    mutate(&next[j]);
    j++;
  }
}

int correct;
int numtests;

void test(prog_t *prog, word_t args[NARGS]) {
  int i;
  word_t res[NRES];

  numtests++;

  exec(prog, args, res);

  for (i = 0; i < NRES; i++) {
    res[i] &= WORDMASK;
  }

  if (!execok) {
    return;
  }

  if(check(args, res)) {
    correct++;
  }
}

int fitness(prog_t *prog) {
  correct = 0;
  numtests = 0;

  tests(prog);

  if (correct == numtests) {
    printf("Found a program with fitness=%d\n", correct);
    print_prog(prog);
    exit(10);
  }

  return correct;
}

int main(void) {
  prog_t pop_a[POPSIZE], pop_b[POPSIZE];
  int i;

  srand(time(NULL));

  for (i = 0; i < POPSIZE; i++) {
    rand_prog(&pop_a[i]);
    rand_prog(&pop_b[i]);
  }

  for (generation = 0; ; generation++) {
    if (PRINT_GEN && (generation % PRINT_GEN) == 0) {
      printf("Generation %d\n", generation);
    }

    if (generation % 2) {
      next_gen(pop_b, pop_a);
    } else {
      next_gen(pop_a, pop_b);
    }
  }

  // NOTREACHED
  return 0;
}
