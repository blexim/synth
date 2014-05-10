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

#define PRINT_GEN 0
#define TEMP_STEP 500000

#ifndef SEED
#define SEED time(NULL)
#endif

extern int execok;

int generation;

double temperature;


void rand_prog(prog_t *prog) {
  int i;

  for (i = 0; i < SZ; i++) {
    prog->ops[i] = rand() % (MAXOPCODE + 1);
  }

  for (i = 0; i < CONSTS; i++) {
    prog->consts[i] = rand() & WORDMASK;
  }

  for (i = 0; i < SZ; i++) {
    prog->params[i*2] = rand() % (i + NARGS + CONSTS);
    prog->params[i*2+1] = rand() % (i + NARGS + CONSTS);
  }
}

int should_mutate() {
  double r = rand();
  return (r / RAND_MAX) <= temperature;
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

  for (i = 0; i < SZ; i++) {
    if (should_mutate()) {
      b->params[i*2] = rand() % (i + NARGS + CONSTS);
    }

    if (should_mutate()) {
      b->params[i*2+1] = rand() % (i + NARGS + CONSTS);
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

int numtests;
int correct;

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

int main(void) {
  prog_t p, best_prog;
  int best_fitness = 0;
  int i;
  int seed = SEED;

  printf("Using random seed: %d\n", seed);
  srand(seed);

  temperature = 1.0;

  rand_prog(&best_prog);
  best_fitness = fitness(&best_prog);

  while (temperature > 0) {
    generation++;

    if (PRINT_GEN && (generation % PRINT_GEN == 0)) {
      printf("Best fitness: %d, target=%d\n", best_fitness, numtests);
    }

    if (generation % ((int) (TEMP_STEP / temperature)) == 0) {
      temperature *= 0.9;

      if (temperature <= 0.001) {
        temperature = 1.0;
      }

      printf("Temperature: %.04f\n", temperature);
    }

    memcpy(&p, &best_prog, sizeof(prog_t));
    mutate(&p);

    int new_fitness = fitness(&p);

    if (new_fitness > best_fitness) {
      generation = 0;
      printf("New best fitness: %d, target=%d\n", new_fitness, numtests);
      best_fitness = new_fitness;
      memcpy(&best_prog, &p, sizeof(prog_t));
    }
  }
}
