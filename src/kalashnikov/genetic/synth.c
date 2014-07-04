//#define _GNU_SOURCE

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <assert.h>

#include <set>

using namespace std;

#ifndef SEARCH
 #define SEARCH
#endif

#include "synth.h"
#include "exec.h"
#include "solution.h"
#include "io.h"


#ifndef POPSIZE
 #define POPSIZE 2000
#endif

#ifndef KEEPLIM
 #define KEEPLIM (POPSIZE/10)
#endif

#ifndef NEWLIM
 #define NEWLIM (POPSIZE/10)
#endif

#ifndef NEWSIZE
 #define NEWSIZE 15
#endif

#ifndef TOURNEYSIZE
 #define TOURNEYSIZE 10
#endif

#ifndef MUTATION_PROB
 #define MUTATION_PROB 0.01
#endif

#ifndef RECOMBINE_PROB
 #define RECOMBINE_PROB 0.1
#endif

#define PRINT_GEN 1000
#define GEN_LIM 0

#ifndef SEED
 #define SEED time(NULL)
#endif

#ifndef SAVEFILE
 #define SAVEFILE "/tmp/geneticsynth"
#endif

#define TESTFILE "/tmp/testvectors"

#define ISTMP(x) ((x) >= NARGS + CONSTS)

#define min(x, y) (x) <= (y) ? (x) : (y)

int generation;
int correct;

unsigned int **test_vectors;

typedef struct {
  solution_t solution;
  int fitness;
} individual_t;

void check_solution(solution_t *solution) {
  int i, j;

  for (i = 0; i < NPROGS; i++) {
    prog_t *prog = &solution->progs[i];

    for (j = 0; j < 3*prog->len; j++) {
      assert((int) prog->params[j] >= 0);
    }
  }
}

void check_population(solution_t *pop) {
  int i;

  for (i = 0; i < POPSIZE; i++) {
    check_solution(&pop[i]);
  }
}

int rand_const() {
  int r = rand() % 5;

  switch (r) {
  case 0:
    return 0;
  case 1:
    return 1;
  case 2:
    return WORDMASK;
  case 3:
    return 1 << (WIDTH - 1);
  case 4:
    return (1 << (WIDTH -1)) - 1;
  }
}


void rand_solution(solution_t *solution) {
  int i, j;

  memset(solution, 0, sizeof(solution_t));

  for (j = 0; j < NPROGS; j++) {
    prog_t *prog = &solution->progs[j];
    prog->len = min(SZ, 1 + (rand() % NEWSIZE));

    for (i = 0; i < prog->len; i++) {
      prog->ops[i] = rand() % (MAXOPCODE + 1);
      prog->params[i*3] = rand() % (i + NARGS + CONSTS);
      prog->params[(i*3)+1] = rand() % (i + NARGS + CONSTS);
      prog->params[(i*3)+2] = rand() % (i + NARGS + CONSTS);
    }

    for (i = 0; i < CONSTS; i++) {
      prog->consts[i] = rand_const();
    }
  }

  for (i = 0; i < NEVARS; i++) {
    solution->evars[i] = rand() & WORDMASK;
  }
}

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

void save(individual_t *pop) {
#ifdef SAVEFILE
  FILE *savefile = fopen(SAVEFILE, "wb");
  size_t written = 0;

  while (written < POPSIZE) {
    written += fwrite(&pop[written], sizeof(individual_t), POPSIZE - written, savefile);
  }

  fclose(savefile);
#endif // SAVEFILE
}

void load(individual_t *pop) {
  size_t nread = 0;

#ifdef SAVEFILE
  FILE *savefile = fopen(SAVEFILE, "rb");
  size_t sz;

  if (savefile == NULL) {
    load_seed(pop);
    return;
  }

  fseek(savefile, 0, SEEK_END);
  sz = ftell(savefile);
  fseek(savefile, 0, SEEK_SET);

  if (sz != POPSIZE * sizeof(individual_t)) {
    load_seed(pop);
  }

  while (nread < POPSIZE && !feof(savefile)) {
    nread += fread(&pop[nread], sizeof(individual_t), POPSIZE - nread, savefile);
  }

  fclose(savefile);
#endif

  while (nread < POPSIZE) {
    individual_t *i = &pop[nread++];
    rand_solution(&i->solution);
    i->fitness = fitness(&i->solution);
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
        b->consts[i] = rand_const();
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

#define splice(p, delta, i) do { \
  if (ISTMP((p))) { \
    (p) -= delta; \
    (p) %= (NARGS + CONSTS + i); \
  } \
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
    int delta = b->len - suffix - prefix;

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

    int k = b->len - suffix;

    for (; i < c->len; i++) {
      c->ops[i + prefix] = b->ops[k];
      c->params[i*3] = b->params[k*3];
      c->params[(i*3)+1] = b->params[(k*3)+1];
      c->params[(i*3)+2] = b->params[(k*3)+2];
      k++;
    }

    for (i = prefix; i < prefix + suffix; i++) {
      splice(c->params[i*3], delta, i);
      splice(c->params[(i*3)+1], delta, i);
      splice(c->params[(i*3)+2], delta, i);
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

int fitness(solution_t *solution) {
  correct = 0;

  for (int i = 0; i < numtests; i++) {
    execok = 1;

    if (check(solution, test_vectors[i]) && execok) {
      correct++;
    }
  }

  return correct;
}

void tournament(solution_t *pop,
    individual_t **a,
    individual_t **b,
    individual_t **c,
    individual_t **d) {
  individual_t *tourney[TOURNEYSIZE];
  individual_t *ind;
  int i, j, idx;
  int already_picked;

  for (i = 0; i < TOURNEYSIZE; i++) {
    idx = rand() % popsize;
    ind = &pop[idx];



      for (j = 0; j < j; j++) {
        if (tourney[j] == ind) {
          already_picked = 1;
          break;
        }
      }
    } while (already_picked);

    tourney[i] = ind;
  }
}

int sol_len(solution_t *s) {
  int ret = 0;
  int i;

  for (i = 0; i < NPROGS; i++) {
    ret += s->progs[i].len;
  }

  return ret;
}

void test(solution_t *solution, word_t args[NARGS]) {
  execok = 1;

  if(check(solution, args) && execok) {
    correct++;
  }
}

int check_fitness(individual_t *i, int best) {
  i->fitness = fitness(i->solution);

  if (i->fitness > best) {
    printf("New best fitness: %d\n", i->fitness);
  }

  if (i->fitness == numtests) {
    print_solution(i->solution);
  }

  return i->fitness;
}

int main(void) {
  int i;
  int seed = SEED;
  int bestfitness = 0;
  int currfitness = 0;
  individual_t *pop = malloc(POPSIZE * sizeof(individual_t));

  printf("Genetic programming using random seed: %d\n", seed);
  srand(seed);

  load(pop);
  load_tests();

  while (bestfitness < numtests) {
    individual_t *a, *b, *c, *d;
    tournament(pop, &a, &b, &c, &d);

    if (do_crossover()) {
      crossover(a, b, c, d);

      bestfitness = max(bestfitness, check_fitness(c, bestfitness));
      bestfitness = max(bestfitness, check_fitness(d, bestfitness));
    } else {
      mutate(a, d);
      bestfitness = max(bestfitness, check_fitness(d, bestfitness));
    }
  }

  save(pop);
  free(pop);

  return 10;
}
