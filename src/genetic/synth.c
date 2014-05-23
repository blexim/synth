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
#define KEEPLIM (POPSIZE/2)
#define KILLLIM (POPSIZE/4)

#define MUTATION_PROB 0.01

#define PRINT_GEN 1000
#define GEN_LIM 0

#ifndef SEED
#define SEED time(NULL)
#endif

#define SAVEFILE "/tmp/geneticsynth"

int generation;
int correct;
int numtests;

void save(solution_t *pop) {
#ifdef SAVEFILE
  FILE *savefile = fopen(SAVEFILE, "wb");
  size_t written = 0;

  while (written < POPSIZE) {
    written += fwrite(&pop[written], sizeof(solution_t), POPSIZE - written, savefile);
  }

  fclose(savefile);
#endif // SAVEFILE
}

void load(solution_t *pop) {
#ifdef SAVEFILE
  FILE *savefile = fopen(SAVEFILE, "rb");
  size_t sz;
  size_t nread = 0;

  if (savefile == NULL) {
    return;
  }

  fseek(savefile, 0, SEEK_END);
  sz = ftell(savefile);
  fseek(savefile, 0, SEEK_SET);

  if (sz != POPSIZE * sizeof(solution_t)) {
    return;
  }

  while (nread < POPSIZE) {
    nread += fread(&pop[nread], sizeof(solution_t), POPSIZE - nread, savefile);
  }

  fclose(savefile);
#endif
}

void rand_solution(solution_t *solution) {
  prog_t *prog = &solution->prog;
  int i;

  for (i = 0; i < SZ; i++) {
    prog->ops[i] = rand() % (MAXOPCODE + 1);
    prog->params[i*3] = rand() % (i + NARGS + CONSTS);
    prog->params[(i*3)+1] = rand() % (i + NARGS + CONSTS);
    prog->params[(i*3)+2] = rand() % (i + NARGS + CONSTS);
  }

  for (i = 0; i < CONSTS; i++) {
    prog->consts[i] = rand() & WORDMASK;
  }
}

int should_mutate() {
  return (rand() < (RAND_MAX * MUTATION_PROB));
}

void mutate(solution_t *solution) {
  prog_t *b = &solution->prog;
  int i;

  for (i = 0; i < SZ; i++) {
    if (should_mutate()) {
      b->ops[i] = rand() % (MAXOPCODE + 1);
    }

    if (should_mutate()) {
      b->params[i*3] = rand() % (i + NARGS + CONSTS);
    }

    if (should_mutate()) {
      b->params[(i*3)+1] = rand() % (i + NARGS + CONSTS);
    }

    if (should_mutate()) {
      b->params[(i*3)+2] = rand() % (i + NARGS + CONSTS);
    }
  }

  for (i = 0; i < CONSTS; i++) {
    if (should_mutate()) {
      b->consts[i] = rand() & WORDMASK;
    }
  }
}

void crossover(solution_t *sol_a, solution_t *sol_b, solution_t *sol_c) {
  prog_t *a = &sol_a->prog;
  prog_t *b = &sol_b->prog;
  prog_t *c = &sol_c->prog;
  int i;

  for (i = 0; i < SZ; i++) {
    if (rand() & 1) {
      c->ops[i] = a->ops[i];
      c->params[i*3] = a->params[i*3];
      c->params[(i*3)+1] = a->params[(i*3)+1];
      c->params[(i*3)+2] = a->params[(i*3)+2];
    } else {
      c->ops[i] = b->ops[i];
      c->params[i*3] = b->params[i*3];
      c->params[(i*3)+1] = b->params[(i*3)+1];
      c->params[(i*3)+2] = b->params[(i*3)+2];
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
}

int fitnesses[POPSIZE];

int fitness(solution_t *solution) {
  correct = 0;
  numtests = 0;

  tests(solution);

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
  solution_t *solutions = (solution_t *) arg;
  int *i1 = (int *) v1;
  int *i2 = (int *) v2;
  prog_t *p1 = &solutions[*i1].prog;
  prog_t *p2 = &solutions[*i2].prog;
  int i;

  for (i = 0; i < SZ; i++) {
    compare_op(p1->ops[i], p2->ops[i]);
    compare_op(p1->params[i*3], p2->params[i*3]);
    compare_op(p1->params[(i*3)+1], p2->params[(i*3)+1]);
    compare_op(p1->params[(i*3)+2], p2->params[(i*3)+2]);
  }

  for (i = 0; i < CONSTS; i++) {
    compare_op(p1->consts[i], p2->consts[i]);
  }

  return 0;
}

int dedup(solution_t *solutions, int *indices) {
  int i, ret, last;
  int sorted[POPSIZE];

  memcpy(sorted, indices, POPSIZE*sizeof(int));
  qsort_r(sorted, POPSIZE, sizeof(int), compare_progs, solutions);

  indices[0] = sorted[0];
  last = sorted[0];
  ret = 1;

  for (i = 1; i < POPSIZE; i++) {
    if (compare_progs(&last, &sorted[i], solutions) != 0) {
      // This is a program we haven't seen before.  Save it.
      indices[ret++] = sorted[i];
      last = sorted[i];
    }
  }

  return ret;
}

int next_gen(solution_t *previous, solution_t *next) {
  int indices[POPSIZE];
  int i, j;
  int idx;
  int maxfit, minfit;
  int nprogs;

  for (i = 0; i < POPSIZE; i++) {
    indices[i] = i;
  }

  //nprogs = dedup(previous, indices);
  nprogs = POPSIZE;

  for (i = 0; i < nprogs; i++) {
    int idx = indices[i];
    fitnesses[idx] = fitness(&previous[idx]);

    if (fitnesses[idx] == numtests) {
      printf("Found a program with fitness=%d\n", correct);
      save(previous);

      print_solution(&previous[idx]);
      exit(10);
    }
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

    memcpy(&next[j], p, sizeof(solution_t));
    j++;
  }

  // Now generate some random individuals.

  int kill;
  int cutoff = minfit+1;

  for (kill = 0;
       kill < KILLLIM && fitnesses[indices[kill]] < cutoff;
       kill++) {
    rand_solution(&next[j]);
    j++;
  }

  if (PRINT_GEN && (generation % PRINT_GEN) == 0) {
    printf("Killed %d, kept %d\n", kill, keep);
  }

  // Finally, let the somewhat-fit individuals from the previous generation breed.

  while (j < POPSIZE) {
    idx = kill + (rand() % (nprogs - kill));
    idx = indices[idx];
    solution_t *a = &previous[idx];

    idx = kill + (rand() % (nprogs - kill));
    idx = indices[idx];
    solution_t *b = &previous[idx];

    crossover(a, b, &next[j]);
    mutate(&next[j]);
    j++;
  }

  return maxfit;
}

void test(solution_t *solution, word_t args[NARGS]) {
  numtests++;

  if(check(solution, args) && execok) {
    correct++;
  }
}

int main(void) {
  solution_t pop_a[POPSIZE], pop_b[POPSIZE];
  int i;
  int seed = SEED;
  int bestfitness = 0;
  int currfitness;

  printf("Genetic programming using random seed: %d\n", seed);
  srand(seed);

  for (i = 0; i < POPSIZE; i++) {
    rand_solution(&pop_a[i]);
    //rand_prog(&pop_b[i]);
  }

  load(pop_a);

  for (generation = 0;
       GEN_LIM == 0 || generation < GEN_LIM;
       generation++) {
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
