#define _GNU_SOURCE

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

#define POPSIZE 2000
#define KEEPLIM (POPSIZE/4)
#define KILLLIM (POPSIZE/4)

#define MUTATION_PROB 0.01

#define PRINT_GEN 1000
#define GEN_LIM 10000

#ifndef SEED
//#define SEED time(NULL)
#endif

extern int execok;

int generation;
int correct;
int numtests;


void rand_prog(prog_t *prog) {
  int i;

  for (i = 0; i < SZ; i++) {
    prog->ops[i] = rand() % (MAXOPCODE + 1);
    prog->params[i*2] = rand() % (i + NARGS + CONSTS);
    prog->params[(i*2)+1] = rand() % (i + NARGS + CONSTS);
  }

  for (i = 0; i < CONSTS; i++) {
    prog->consts[i] = rand() & WORDMASK;
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

    if (should_mutate()) {
      b->params[i*2] = rand() % (i + NARGS + CONSTS);
    }

    if (should_mutate()) {
      b->params[(i*2)+1] = rand() % (i + NARGS + CONSTS);
    }
  }

  for (i = 0; i < CONSTS; i++) {
    if (should_mutate()) {
      b->consts[i] = rand() & WORDMASK;
    }
  }
}

void crossover(prog_t *a, prog_t *b, prog_t *c) {
  int i;

  for (i = 0; i < SZ; i++) {
    if (rand() & 1) {
      c->ops[i] = a->ops[i];
      c->params[i*2] = a->params[i*2];
      c->params[(i*2)+1] = a->params[(i*2)+1];
    } else {
      c->ops[i] = b->ops[i];
      c->params[i*2] = b->params[i*2];
      c->params[(i*2)+1] = b->params[(i*2)+1];
    }
  }

  for (i = 0; i < CONSTS; i++) {
    if (rand() & 1) {
      c->consts[i] = a->consts[i];
    } else {
      c->consts[i] = b->consts[i];
    }
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


int compare_fitness(const void *v1, const void *v2) {
  int *i1 = (int *) v1;
  int *i2 = (int *) v2;
  int f1 = fitnesses[*i1];
  int f2 = fitnesses[*i2];

  return f1 - f2;
}

#define compare_op(x, y) do { \
  if ((x) < (y)) return -1; \
  else if ((x) > (y)) return 1; \
} while(0)

int compare_progs(const void *v1, const void *v2, void *arg) {
  prog_t *progs = (prog_t *) arg;
  int *i1 = (int *) v1;
  int *i2 = (int *) v2;
  prog_t *p1 = &progs[*i1];
  prog_t *p2 = &progs[*i2];
  int i;

  for (i = 0; i < SZ; i++) {
    compare_op(p1->ops[i], p2->ops[i]);
    compare_op(p1->params[i*2], p2->params[i*2]);
    compare_op(p1->params[(i*2)+1], p2->params[(i*2)+1]);
  }

  for (i = 0; i < CONSTS; i++) {
    compare_op(p1->consts[i], p2->consts[i]);
  }

  return 0;
}

int dedup(prog_t *progs, int *indices) {
  int i, ret, last;
  int sorted[POPSIZE];

  memcpy(sorted, indices, POPSIZE*sizeof(int));
  qsort_r(sorted, POPSIZE, sizeof(int), compare_progs, progs);

  indices[0] = sorted[0];
  last = sorted[0];
  ret = 1;

  for (i = 1; i < POPSIZE; i++) {
    if (compare_progs(&last, &sorted[i], progs) != 0) {
      // This is a program we haven't seen before.  Save it.
      indices[ret++] = sorted[i];
      last = sorted[i];
    }
  }

  return ret;
}

int next_gen(prog_t *previous, prog_t *next) {
  int indices[POPSIZE];
  int i, j;
  int idx;
  int maxfit, minfit;
  int nprogs;

  for (i = 0; i < POPSIZE; i++) {
    indices[i] = i;
  }

  nprogs = dedup(previous, indices);

  for (i = 0; i < nprogs; i++) {
    int idx = indices[i];
    fitnesses[idx] = fitness(&previous[idx]);
  }

  qsort(indices, nprogs, sizeof(int), compare_fitness);

  maxfit = fitnesses[indices[nprogs - 1]];
  minfit = fitnesses[indices[0]];

  if (PRINT_GEN && (generation % PRINT_GEN) == 0) {
    printf("Unique programs: %d\n", nprogs);
    printf("Fittest: %d, least fit: %d\n", maxfit, minfit);
    printf("Target: %d\n", numtests);
  }

  // Copy the fittest individuals straight into the next generation.
  j = 0;

  int keep;

  for (keep = 0;
       keep < KEEPLIM && fitnesses[indices[nprogs - keep - 1]] == maxfit;
       keep++) {
    idx = indices[nprogs - keep - 1];
    prog_t *p = &previous[idx];

    memcpy(&next[j], p, sizeof(prog_t));
    j++;
  }

  // Now generate some random individuals.

  int kill;
  int cutoff = minfit+1;

  for (kill = 0;
       kill < KILLLIM && fitnesses[indices[kill]] < cutoff;
       kill++) {
    rand_prog(&next[j]);
    j++;
  }

  if (PRINT_GEN && (generation % PRINT_GEN) == 0) {
    printf("Killed %d, kept %d\n", kill, keep);
  }

  // Finally, let the somewhat-fit individuals from the previous generation breed.

  while (j < POPSIZE) {
    idx = kill + (rand() % (nprogs - kill));
    idx = indices[idx];
    prog_t *a = &previous[idx];

    idx = kill + (rand() % (nprogs - kill));
    idx = indices[idx];
    prog_t *b = &previous[idx];

    crossover(a, b, &next[j]);
    mutate(&next[j]);
    j++;
  }

  return maxfit;
}

void test(prog_t *prog, word_t args[NARGS]) {
  numtests++;
  execok = 1;

  if(check(prog, args) && execok) {
    correct++;
  }
}

int main(void) {
  prog_t pop_a[POPSIZE], pop_b[POPSIZE];
  int i;
  int seed = SEED;
  int bestfitness = 0;
  int currfitness;

  printf("Using random seed: %d\n", seed);
  srand(seed);

  for (i = 0; i < POPSIZE; i++) {
    rand_prog(&pop_a[i]);
    //rand_prog(&pop_b[i]);
  }

  for (generation = 0; generation < GEN_LIM; generation++) {
    if (PRINT_GEN && (generation % PRINT_GEN) == 0) {
      printf("Generation %d, best=%d\n", generation, bestfitness);
    }

    if (generation & 1) {
      currfitness = next_gen(pop_b, pop_a);
    } else {
      currfitness = next_gen(pop_a, pop_b);
    }

    if (currfitness > bestfitness) {
      printf("Best fitness: %d\n", currfitness);
      bestfitness = currfitness;
      generation = 0;
    }
  }

  // NOTREACHED
  return 0;
}
