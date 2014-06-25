//#define _GNU_SOURCE

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#ifndef SEARCH
 #define SEARCH
#endif

#include "synth.h"
#include "exec.h"
#include "solution.h"

#define WORDMASK ((1 << WIDTH) - 1)
//#define WORDMASK 0xffffffff
#define PMASK ((1 << PWIDTH) - 1)
#define OPMASK ((1 << OPLEN) - 1)

#define POPSIZE 200
#define KEEPLIM (POPSIZE/2)
#define KILLLIM (POPSIZE/4)

#define MUTATION_PROB 0.01
#define RECOMBINE_PROB 0.1

#define PRINT_GEN 1000
#define GEN_LIM 0

#ifndef SEED
#define SEED time(NULL)
#endif

#define SAVEFILE "/tmp/geneticsynth"

int generation;
int correct;
int numtests;

void load_seed(solution_t *pop) {
#ifdef SEEDFILE
  FILE *seedfile = fopen(SAVEFILE, "rb");
  size_t nread = 0;

  if (seedfile == NULL) {
    return;
  }

  while (!feof(seedfile) && !ferror(seedfile)) {
    nread += fread(&pop[nread], sizeof(solution_t), 1, savefile);
  }

  printf("Seeded %d programs\n", nread);

  fclose(seedfile);
#endif
}

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
    load_seed(pop);
    return;
  }

  fseek(savefile, 0, SEEK_END);
  sz = ftell(savefile);
  fseek(savefile, 0, SEEK_SET);

  if (sz != POPSIZE * sizeof(solution_t)) {
    load_seed(pop);
  }

  while (nread < POPSIZE) {
    nread += fread(&pop[nread], sizeof(solution_t), POPSIZE - nread, savefile);
  }

  fclose(savefile);
#endif
}

void rand_solution(solution_t *solution) {
  int i, j;

  for (j = 0; j < NPROGS; j++) {
    prog_t *prog = &solution->progs[j];
    prog->len = 5;

    for (i = 0; i < prog->len; i++) {
      prog->ops[i] = rand() % (MAXOPCODE + 1);
      prog->params[i*3] = rand() % (i + NARGS + CONSTS);
      prog->params[(i*3)+1] = rand() % (i + NARGS + CONSTS);
      prog->params[(i*3)+2] = rand() % (i + NARGS + CONSTS);
    }

    for (i = 0; i < CONSTS; i++) {
      prog->consts[i] = rand() & WORDMASK;
    }
  }

  for (i = 0; i < NEVARS; i++) {
    solution->evars[i] = rand() & WORDMASK;
  }
}

int should_mutate() {
  return (rand() < (RAND_MAX * MUTATION_PROB));
}

int should_recombine() {
  return (rand() < (RAND_MAX * RECOMBINE_PROB));
}

void mutate(solution_t *solution) {
  int i, j;

  for (j = 0; j < NPROGS; j++) {
    prog_t *b = &solution->progs[j];

    for (i = 0; i < b->len; i++) {
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

  for (i = 0; i < NEVARS; i++) {
    if (should_mutate()) {
      solution->evars[i] = rand() & WORDMASK;
    }
  }
}

#define recombine() do { \
  if (should_recombine()) { tmp = a; a = b; b = tmp; } \
} while(0)

#define recombine_sol() do { \
  if (should_recombine()) { tmp_sol = sol_a; sol_a = sol_b; sol_b = tmp_sol; } \
} while(0)

void crossover(solution_t *sol_a, solution_t *sol_b, solution_t *sol_c) {
  prog_t *tmp;
  solution_t *tmp_sol;
  int i, j;

  for (j = 0; j < NPROGS; j++) {
    prog_t *a = &sol_a->progs[j];
    prog_t *b = &sol_b->progs[j];
    prog_t *c = &sol_c->progs[j];

    int prefix = rand() % (a->len + 1);
    int suffix = rand() % (b->len + 1);

    if (prefix + suffix > SZ) {
      if (prefix > suffix) {
        prefix = SZ - suffix;
      } else {
        suffix = SZ - prefix;
      }
    }

    c->len = prefix + suffix;

    for (i = 0; i < prefix; i++) {
      c->ops[i] = a->ops[i];
      c->params[i*3] = a->params[i*3];
      c->params[(i*3)+1] = a->params[(i*3)+1];
      c->params[(i*3)+2] = a->params[(i*3)+2];
    }

    for (i = prefix; i < (prefix + suffix); i++) {
      c->ops[i] = b->ops[i];
      c->params[i*3] = b->params[i*3];
      c->params[(i*3)+1] = b->params[(i*3)+1];
      c->params[(i*3)+2] = b->params[(i*3)+2];
    }

    for (i = 0; i < CONSTS; i++) {
      recombine();
      c->consts[i] = a->consts[i];
    }
  }

  for (i = 0; i < NEVARS; i++) {
    recombine_sol();
    sol_c->evars[i] = sol_a->evars[i];
  }
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

int next_gen(solution_t *previous, solution_t *next) {
  int indices[POPSIZE];
  int i, j;
  int idx;
  int maxfit, minfit;
  int nprogs;

  for (i = 0; i < POPSIZE; i++) {
    indices[i] = i;
  }

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
    solution_t *p = &previous[idx];

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

  execok = 1;

  if(check(solution, args) && execok) {
    correct++;
  }
}

int main(void) {
  solution_t *pop_a = malloc(POPSIZE * sizeof(solution_t));
  solution_t *pop_b = malloc(POPSIZE * sizeof(solution_t));
  int i;
  int seed = SEED;
  int bestfitness = 0;
  int currfitness;

  printf("Genetic programming using random seed: %d\n", seed);
  srand(seed);

  for (i = 0; i < POPSIZE; i++) {
    rand_solution(&pop_a[i]);
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
