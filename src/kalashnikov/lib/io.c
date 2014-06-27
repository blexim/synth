#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

#include "synth.h"

#define TESTFILE "/tmp/testvectors"
#define SOLFILE "/tmp/solution"

unsigned int **test_vectors;
int numtests;

#define getline(f) do { \
  fgets(buf, sizeof(buf), f); \
  p = buf; \
} while (0)

#define getint(x) do { \
  (x) = strtol(p, &q, 0); \
  assert(q > p); \
} while(0)


void load_tests() {
  FILE *testfile = fopen(TESTFILE, "r");
  assert(testfile != NULL);

  char buf[1024];
  char *p, *q;

  // Format of the file is:
  // <number of tests>
  // <test 1>
  // <test 2>
  // ...
  getline(testfile);
  getint(numtests);

  test_vectors = malloc(numtests * sizeof(int *));

  for (int i = 0; i < numtests; i++) {
    test_vectors[i] = malloc(NARGS * sizeof(int));

    getline(testfile);

    printf("Test vector %d: ", i);

    for (int j = 0; j < NARGS; j++) {
      getint(test_vectors[i][j]);
      printf("%d ", test_vectors[i][j]);
    }

    printf("\n");
  }

  fclose(testfile);
}

void free_tests() {
  int i, j;

  for (i = 0; i < numtests; i++) {
    free(test_vectors[i]);
  }

  free(test_vectors);
}

void load_solution(solution_t *solution) {
  FILE *solfile = fopen(SOLFILE, "r");
  assert(solfile != NULL);

  memset(solution, 0, sizeof(solution_t));

  char buf[1024];
  char *p, *q;

  // Format of the file is:
  //
  // <evar1> <evar2> ...
  // <n1-instructions>
  // <opcode1> <param11> <param12> <param13>
  // ...
  // <const1>
  // <const2>
  // ...
  // <n2-instructions><n2-consts>
  // ...

  getline(solfile);

  for (int i = 0; i < NEVARS; i++) {
    getint(solution->evars[i]);
  }

  for (int i = 0; i < NPROGS; i++) {
    prog_t *prog = &solution->progs[i];

    getline(solfile);
    getint(prog->len);

    for (int j = 0; j < prog->len; j++) {
      getline(solfile);

      getint(prog->ops[j]);
      getint(prog->params[3*j]);
      getint(prog->params[3*j + 1]);
      getint(prog->params[3*j + 2]);
    }

    for (int j = 0; j < CONSTS; j++) {
      getline(solfile);
      getint(prog->consts[j]);
    }
  }

  fclose(solfile);
}
