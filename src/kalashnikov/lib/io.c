#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

#include "synth.h"

#define TESTFILE "/tmp/testvectors"

unsigned int **test_vectors;
int numtests;

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
  fgets(buf, sizeof(buf) - 1, testfile);
  numtests = strtol(buf, &p, 0);
  assert(p > buf);

  test_vectors = malloc(numtests * sizeof(int *));

  for (int i = 0; i < numtests; i++) {
    test_vectors[i] = malloc(NARGS * sizeof(int));

    fgets(buf, sizeof(buf) - 1, testfile);

    p = buf;

    printf("Test vector %d: ", i);

    for (int j = 0; j < NARGS; j++) {
      test_vectors[i][j] = strtol(p, &q, 0);
      assert(q > p);
      p = q;

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
