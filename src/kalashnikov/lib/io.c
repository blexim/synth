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
  (x) = strtoul(p, &q, 0); \
  assert(q > p); \
  p = q; \
} while(0)


void load_tests() {
  FILE *testfile = fopen(TESTFILE, "r");

  if (testfile == NULL) {
    numtests = 0;
    return;
  }

  char buf[8192];
  char *p, *q;

  int i, j;

  // Format of the file is:
  // <number of tests>
  // <test 1>
  // <test 2>
  // ...
  getline(testfile);
  getint(numtests);

  test_vectors = (unsigned int **) malloc(numtests * sizeof(int *));

  for (i = 0; i < numtests; i++) {
    test_vectors[i] = (unsigned int *) malloc(NARGS * sizeof(int));

    getline(testfile);

    printf("Test vector %d: ", i);

    for (j = 0; j < NARGS; j++) {
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

  int i, j;
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
  // <n2-instructions>
  // ...

  getline(solfile);

  printf("Evars: ");

  for (i = 0; i < NEVARS; i++) {
    getint(solution->evars[i]);
    printf("0x%x ", solution->evars[i]);
  }

  for (i = 0; i < NPROGS; i++) {
    printf("\nProg %d:\n", i);

    prog_t *prog = &solution->progs[i];

    getline(solfile);
    getint(prog->len);

    for (j = 0; j < prog->len; j++) {
      getline(solfile);

      getint(prog->ops[j]);
      getint(prog->params[3*j]);
      getint(prog->params[3*j + 1]);
      getint(prog->params[3*j + 2]);

      printf("0x%x 0x%x 0x%x 0x%x\n",
          prog->ops[j],
          prog->params[3*j],
          prog->params[3*j + 1],
          prog->params[3*j + 2]);
    }

    for (j = 0; j < CONSTS; j++) {
      getline(solfile);
      getint(prog->consts[j]);

      printf("Const: 0x%x\n", prog->consts[j]);
    }
  }

  fclose(solfile);
}
