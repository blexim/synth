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

#define PRINT_GEN 0
#define TEMP_STEP 500000

#ifndef SEED
#define SEED time(NULL)
#endif

#define SAVEFILE "/tmp/annealsynth"

int generation;

double temperature;

void save(solution_t *solution) {
#ifdef SAVEFILE
  FILE *f = fopen(SAVEFILE, "wb");
  fwrite(solution, sizeof(solution_t), 1, f);
  fclose(f);
#endif
}

void load(solution_t *solution) {
#ifdef SAVEFILE
  FILE *f = fopen(SAVEFILE, "rb");
  size_t sz;

  if (f == NULL) {
    return;
  }

  fseek(f, 0, SEEK_END);
  sz = ftell(f);
  fseek(f, 0, SEEK_SET);

  if (sz == sizeof(solution_t)) {
    while (fread(solution, sizeof(solution_t), 1, f) == 0);
  }

  fclose(f);
#endif
}

void rand_solution(solution_t *solution) {
  int i, j;

  for (j = 0; j < NPROGS; j++) {
    prog_t *prog = &solution->progs[j];
    prog->len = SZ;

    for (i = 0; i < prog->len; i++) {
      prog->ops[i] = rand() % (MAXOPCODE + 1);
    }

    for (i = 0; i < CONSTS; i++) {
      prog->consts[i] = rand() & WORDMASK;
    }

    for (i = 0; i < prog->len; i++) {
      prog->params[i*3] = rand() % (i + ARGBASE);
      prog->params[i*3+1] = rand() % (i + ARGBASE);
      prog->params[i*3+2] = rand() % (i + ARGBASE);
    }
  }

  for (i = 0; i < NEVARS; i++) {
    solution->evars[i] = rand() & WORDMASK;
  }
}

int should_mutate() {
  double r = rand();
  return (r / RAND_MAX) <= temperature;
}

void mutate(solution_t *solution) {
  int i, j;

  for (j = 0; j < NPROGS; j++) {
    prog_t *b = &solution->progs[j];

    for (i = 0; i < b->len; i++) {
      if (should_mutate()) {
        b->ops[i] = rand() % (MAXOPCODE + 1);
      }
    }

    for (i = 0; i < CONSTS; i++) {
      if (should_mutate()) {
        b->consts[i] = rand() & WORDMASK;
      }
    }

    for (i = 0; i < b->len; i++) {
      if (should_mutate()) {
        b->params[i*3] = rand() % (i + ARGBASE);
      }

      if (should_mutate()) {
        b->params[i*3+1] = rand() % (i + ARGBASE);
      }

      if (should_mutate()) {
        b->params[i*3+2] = rand() % (i + ARGBASE);
      }
    }
  }

  for (i = 0; i < NEVARS; i++) {
    if (should_mutate()) {
      solution->evars[i] = rand() & WORDMASK;
    }
  }
}


int numtests;
int correct;

int fitness(solution_t *solution) {
  correct = 0;
  numtests = 0;

  tests(solution);

  if (correct == (numtests * MAXFIT)) {
    printf("Found a program with fitness=%d\n", correct);
    save(solution);
    print_solution(solution);
    exit(10);
  }

  return correct;
}


void test(solution_t *solution, word_t args[NARGS]) {
  numtests++;

  execok = 1;

  int score = check(solution, args);
  
  if (execok) {
    correct += score;
  }
}

int main(void) {
  solution_t solution, best_solution;
  int best_fitness = 0;
  int i;
  int seed = SEED;

  printf("Annealing using random seed: %d\n", seed);
  srand(seed);

  temperature = 1.0;

  rand_solution(&best_solution);
  load(&best_solution);
  best_fitness = fitness(&best_solution);

  while (temperature > 0) {
    generation++;

    if (PRINT_GEN && (generation % PRINT_GEN == 0)) {
      printf("Best fitness: %d, target=%d\n", best_fitness, numtests * MAXFIT);
    }

    if (generation % ((int) (TEMP_STEP / temperature)) == 0) {
      temperature *= 0.9;

      if (temperature <= 0.001) {
        temperature = 1.0;
      }

      printf("Temperature: %.04f\n", temperature);
    }

    memcpy(&solution, &best_solution, sizeof(solution_t));
    mutate(&solution);

    int new_fitness = fitness(&solution);

    if (new_fitness > best_fitness) {
      generation = 0;
      printf("New best fitness: %d, target=%d\n", new_fitness, numtests);
      best_fitness = new_fitness;
      memcpy(&best_solution, &solution, sizeof(solution_t));
    }
  }
}
