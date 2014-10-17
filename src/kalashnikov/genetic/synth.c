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

#ifndef REPLACE_PROB
 #define REPLACE_PROB 0.15
#endif

#ifndef RECOMBINE_PROB
 #define RECOMBINE_PROB 0.1
#endif

#ifndef GENERAL_SET
 #define GENERAL_SET 1
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

#define ISTMP(x) ((x) >= ARGBASE)

#define min(x, y) (x) <= (y) ? (x) : (y)

int generation;
int correct;
int target;

extern unsigned int **test_vectors;

typedef struct {
  solution_t solution;
  int fitness;
} individual_t;

int fitness(solution_t *solution) {
  correct = 0;

  for (int i = GENERAL_SET; i < numtests; i++) {
    execok = 1;
    int score = 0;

    score = check(solution, test_vectors[i]);

    if (execok) {
      correct += score;
    }
  }

  return correct;
}

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
      prog->params[i*3] = rand() % (i + ARGBASE);
      prog->params[(i*3)+1] = rand() % (i + ARGBASE);
      prog->params[(i*3)+2] = rand() % (i + ARGBASE);
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
    //load_seed(pop);
    return;
  }

  fseek(savefile, 0, SEEK_END);
  sz = ftell(savefile);
  fseek(savefile, 0, SEEK_SET);

  if (sz != POPSIZE * sizeof(individual_t)) {
    //load_seed(pop);
  }

  while (nread < POPSIZE && !feof(savefile)) {
    nread += fread(&pop[nread], sizeof(individual_t), POPSIZE - nread, savefile);
  }

  fclose(savefile);
#endif

  while (nread < POPSIZE) {
    individual_t *i = &pop[nread++];
    rand_solution(&i->solution);
  }
}



int should_mutate() {
  return (rand() < (RAND_MAX * MUTATION_PROB));
}

int should_replace() {
  return (rand() < (RAND_MAX * REPLACE_PROB));
}

int should_recombine() {
  return (rand() < (RAND_MAX * RECOMBINE_PROB));
}

void mutate(individual_t *a, individual_t *b) {
  memcpy(b, a, sizeof(individual_t));

  solution_t *sb = &b->solution;

  int ntargets = 0;
  int i;

  ntargets += NEVARS;

  for (i = 0; i < NPROGS; i++) {
    ntargets += 4 * sb->progs[i].len;
    ntargets += CONSTS;
  }

  if (ntargets == 0) {
    b->fitness = 0;
    return;
  }

  int target = rand() % ntargets;

  if (target < NEVARS) {
    sb->evars[target] = rand() & WORDMASK;
    return;
  }

  target -= NEVARS;

  for (i = 0; i < NPROGS; i++) {
    if (target < 4 * sb->progs[i].len) {
      int offs = target % 4;
      target /= 4;

      if (offs % 4 == 3) {
        sb->progs[i].ops[target] = rand() % MAXOPCODE;
      } else {
        sb->progs[i].params[target*3 + offs] = rand() % (ARGBASE + target);
      }

      return;
    }

    target -= 4 * sb->progs[i].len;

    if (target < CONSTS) {
      sb->progs[i].consts[target] = rand_const();
    }
  }
}

#define splice(p, delta, i) do { \
  if (ISTMP((p))) { \
    (p) -= delta; \
    (p) %= (ARGBASE + i); \
  } \
} while(0)

void crossover(individual_t *a,
               individual_t *b,
               individual_t *c,
               individual_t *d) {
  int i, j;
  j = rand() % NPROGS;

  prog_t *pa = &a->solution.progs[j];
  prog_t *pb = &b->solution.progs[j];
  prog_t *pc = &c->solution.progs[j];
  prog_t *pd = &d->solution.progs[j];

  int a_switch = rand() % (pa->len + 1);
  int b_switch;

  int b_lower = a_switch + pb->len - SZ;
  b_lower = b_lower < 0 ? 0 : b_lower;

  int b_upper = a_switch - pa->len + SZ;
  b_upper = b_upper > pb->len ? pb->len : b_upper;

  int b_range = b_upper - b_lower;

  assert(b_lower >= 0);


  if (b_range == 0) {
    b_switch = 0;
  } else {
    b_switch = b_lower + (rand() % (b_range));
  }

  int c_len = a_switch + pb->len - b_switch;
  int d_len = b_switch + pa->len - a_switch;

  for (i = 0; i < a_switch; i++) {
    pc->ops[i] = pa->ops[i];
    pc->params[i*3] = pa->params[i*3];
    pc->params[(i*3)+1] = pa->params[(i*3)+1];
    pc->params[(i*3)+2] = pa->params[(i*3)+2];
  }

  for (i = a_switch, j = b_switch; j < pd->len; i++, j++) {
    pc->ops[i] = pb->ops[j];
    pc->params[i*3] = pb->params[j*3];
    pc->params[(i*3)+1] = pb->params[(j*3)+1];
    pc->params[(i*3)+2] = pb->params[(j*3)+2];

    splice(pc->params[i*3], j - i, i);
    splice(pc->params[(i*3)+1], j - i, i);
    splice(pc->params[(i*3)+2], j - i, i);
  }

  for (i = 0; i < b_switch; i++) {
    pd->ops[i] = pb->ops[i];
    pd->params[i*3] = pb->params[i*3];
    pd->params[(i*3)+1] = pb->params[(i*3)+1];
    pd->params[(i*3)+2] = pb->params[(i*3)+2];
  }

  for (i = b_switch, j = a_switch; j < pd->len; i++, j++) {
    pd->ops[i] = pa->ops[j];
    pd->params[i*3] = pa->params[j*3];
    pd->params[(i*3)+1] = pa->params[(j*3)+1];
    pd->params[(i*3)+2] = pa->params[(j*3)+2];

    splice(pd->params[i*3], j - i, i);
    splice(pd->params[(i*3)+1], j - i, i);
    splice(pd->params[(i*3)+2], j - i, i);
  }

  for (i = 0; i < NEVARS; i++) {
    c->solution.evars[i] = a->solution.evars[i];
    d->solution.evars[i] = b->solution.evars[i];
  }

  for (i = 0; i < CONSTS; i++) {
    pc->consts[i] = pa->consts[i];
    pd->consts[i] = pb->consts[i];
  }
}



void tournament(individual_t *pop,
    individual_t **a,
    individual_t **b,
    individual_t **c,
    individual_t **d) {
  individual_t *ind;
  int entrants = 0;

  *a = NULL;
  *b = NULL;
  *c = NULL;
  *d = NULL;

  while (entrants < TOURNEYSIZE) {
    int idx = rand() % POPSIZE;
    ind = &pop[idx];

    if (ind == *a ||
        ind == *b ||
        ind == *c ||
        ind == *d) {
      continue;
    }

    entrants++;

    if (*a == NULL) {
      *b = *a;
      *a = ind;
    } else if (*b == NULL) {
      *b = ind;
    } else if (*d == NULL) {
      *c = *d;
      *d = ind;
    } else if (*c == NULL) {
      *c = ind;
    } else if ((*a)->fitness < ind->fitness) {
      *b = *a;
      *a = ind;
    } else if ((*b)->fitness < ind->fitness) {
      *b = ind;
    } else if ((*d)->fitness > ind->fitness) {
      *c = *d;
      *d = ind;
    } else if ((*c)->fitness > ind->fitness) {
      *c = ind;
    }
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

  int score = check(solution, args);

  if (execok) {
    correct += score;
  }
}

int check_fitness(individual_t *i, int best) {
  i->fitness = fitness(&i->solution);

  if (i->fitness > best) {
    printf("New best fitness: %d\n", i->fitness);
  }

  return i->fitness;
}

int check_generalise(individual_t *ind) {
  correct = 0;

  for (int i = 0; i < GENERAL_SET; i++) {
    execok = 1;

    int score = check(&ind->solution, test_vectors[i]);
    
    if (execok) {
      correct += score;
    }
  }

  return correct;
}

int main(void) {
  int i;
  int seed = SEED;
  int bestfitness = 0;
  int currfitness = 0;
  int done = 0;
  individual_t *pop = (individual_t *) malloc(POPSIZE * sizeof(individual_t));

  printf("Genetic programming using random seed: %d\n", seed);
  srand(seed);

  load(pop);
  load_tests();

  target = (numtests - GENERAL_SET) * MAXFIT;
  printf("Target fitness: %d\n", target);

  for (i = 0; i < POPSIZE; i++) {
    individual_t *ind = &pop[i];
    bestfitness = max(bestfitness, check_fitness(ind, bestfitness));

    if (ind->fitness == target && check_generalise(ind)) {
      print_solution(&ind->solution);
      done = 1;
      break;
    }
  }


  while (!done) {
    individual_t *a, *b, *c, *d;
    tournament(pop, &a, &b, &c, &d);

    if (should_mutate()) {
      assert(a != d);
      mutate(a, d);
      bestfitness = max(bestfitness, check_fitness(d, bestfitness));
    } else if (should_replace()) {
      rand_solution(&d->solution);
      bestfitness = max(bestfitness, check_fitness(d, bestfitness));
    } else {
      crossover(a, b, c, d);

      bestfitness = max(bestfitness, check_fitness(c, bestfitness));
      bestfitness = max(bestfitness, check_fitness(d, bestfitness));
    }

    if (c->fitness == target) {
      print_solution(&c->solution);
      done = 1;
    } else if (d->fitness == target) {
      print_solution(&d->solution);
      done = 1;
    }
  }


  save(pop);
  free(pop);

  return 10;
}
