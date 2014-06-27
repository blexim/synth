//#define _GNU_SOURCE

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <assert.h>

#ifndef SEARCH
 #define SEARCH
#endif

#include "synth.h"
#include "exec.h"
#include "solution.h"


#define POPSIZE 5000
#define KEEPLIM (POPSIZE/10)
#define NEWLIM (POPSIZE/10)

#define NEWSIZE 5

#define TOURNEYSIZE 5
#define GEN_SIZE 5

#define MUTATION_PROB 0.01
#define RECOMBINE_PROB 0.1

#define PRINT_GEN 1000
#define GEN_LIM 0

#ifndef SEED
#define SEED time(NULL)
#endif

#define SAVEFILE "/tmp/geneticsynth"

#define ISTMP(x) ((x) >= NARGS + CONSTS)

#define min(x, y) ((x) < (y) ? (x) : (y))

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
    prog->len = min(SZ, 1 + (rand() % NEWSIZE));

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

#define splice(p, delta) do { \
  if (ISTMP((p))) (p) -= delta; \
  if ((p) < 0) (p) = 0; \
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
      splice(c->params[i*3], delta);
      splice(c->params[(i*3)+1], delta);
      splice(c->params[(i*3)+2], delta);
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

solution_t *pick_parent(solution_t *pop, int *fitnesses, int maxfit, int minfit, int popsize) {
  solution_t *tourney[TOURNEYSIZE];
  int cutoffs[TOURNEYSIZE];
  int total = 0;

  for (int i = 0; i < TOURNEYSIZE; i++) {
    int idx = rand() % popsize;
    solution_t *s = &pop[idx];
    int fit = fitnesses[idx];

    tourney[i] = s;
    cutoffs[i] = total + fit;
    total += fit;
  }

  if (total == 0) {
    return tourney[0];
  }

  int winner = rand() % total;

  for (int i = 0; i < TOURNEYSIZE; i++) {
    if (winner < cutoffs[i]) {
      return tourney[i];
    }
  }

  assert(0);
}

int sol_len(solution_t *s) {
  int ret = 0;
  int i;

  for (i = 0; i < NPROGS; i++) {
    ret += s->progs[i].len;
  }

  return ret;
}

int next_gen(solution_t *previous, solution_t *next) {
  int i, j;
  int maxfit, minfit;
  int maxlen, minlen;
  int nprogs;

  nprogs = POPSIZE;
  maxfit = -1;
  minfit = -1;
  maxlen = -1;
  minlen = -1;

  for (i = 0; i < nprogs; i++) {
    int fit = fitness(&previous[i]);
    int len = sol_len(&previous[i]);

    if (fit == numtests) {
      printf("Found a program with fitness=%d\n", correct);
      save(previous);

      print_solution(&previous[i]);

      free(previous);
      free(next);

      exit(10);
    }

    fit = (fit * 5) - len;

    if (fit < 0) {
      fit = 0;
    }

    if (maxfit == -1 || fit > maxfit) {
      maxfit = fit;
    }

    if (minfit == -1 || fit < minfit) {
      minfit = fit;
    }

    if (maxlen == -1 || len > maxlen) {
      maxlen = len;
    }

    if (minlen == -1 || len < minlen) {
      minlen = len;
    }

    fitnesses[i] = fit;
  }

  if (PRINT_GEN && (generation % PRINT_GEN) == 0) {
    printf("Unique programs: %d\n", nprogs);
    printf("Fittest: %d, least fit: %d\n", maxfit, minfit);
    printf("Target: %d\n", numtests);
  }

  for (i = 0; i < NEWLIM; i++) {
    rand_solution(&next[i]);
  }

  for (j = 0; j < nprogs && i < NEWLIM + KEEPLIM; j++) {
    if (fitnesses[j] == maxfit) {
      memcpy(&next[i], &previous[j], sizeof(solution_t));
      i++;
    }
  }


  for (; i < POPSIZE; i++) {
    solution_t *a = pick_parent(previous, fitnesses, maxfit, minfit, nprogs);
    solution_t *b = pick_parent(previous, fitnesses, maxfit, minfit, nprogs);
    solution_t *c = &next[i];

    a = &previous[0];

    crossover(a, b, c);
    mutate(c);
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
  int currfitness = 0;

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
