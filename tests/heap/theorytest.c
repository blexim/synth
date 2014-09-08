#define NHEAP 4
#define NARGS 16

#define SEARCH

#include "synth.h"
#include "heaptheory.h"

#include <assert.h>

int main(void) {
  word_t matrix[NARGS];
  word_t matrix2[NARGS];

  word_t w = 0;
  word_t x = 1;
  word_t y = 2;
  word_t z = 3;

  int i;

  for (i = 0; i < NARGS; i++) {
    matrix[i] = INF;
  }

  for (i = 0; i < NHEAP; i++) {
    matrix[idx(i, i)] = 0;
  }

  matrix[idx(x, y)] = 0;
  matrix[idx(y, x)] = 0;

  matrix[idx(x, w)] = 1;
  matrix[idx(y, w)] = 1;

  update(matrix, matrix2, x, z);


  printf("y -> x = %d (expect 0)\n", path_length(matrix2, y, x));
  printf("x -> z = %d (expect 1)\n", path_length(matrix2, x, z));
  printf("y -> z = %d (expect 1)\n", path_length(matrix2, y, z));
  printf("y -> w = %d (expect -1)\n", path_length(matrix2, y, w));
}
