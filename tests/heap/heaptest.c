#include <stdio.h>
#include <assert.h>

#include "heaptheory.h"
#include "synth.h"

#define x 0
#define y 1
#define z 2

void print_heap(word_t vars[NARGS]) {
  int a, b;

  for (a = 0; a < NHEAP; a++) {
    for (b = 0; b < NHEAP; b++) {
      unsigned int ab = path_length(vars, a, b);

      if (ab == INF) {
        printf("%10s", "INF");
      } else {
        printf("%10x", ab);
      }
    }

    printf("\n");
  }
}

void test1(void) {
  word_t pre[NARGS] = { 0, 2147483648, INF, INF, 0, INF, INF, INF, 0 };
  word_t post[NARGS];

  assert(well_formed(pre));
  update(pre, post, x, y);

  print_heap(pre);
  printf("x->n = y\n");
  print_heap(post);

  if (!well_formed(post)) {
    printf("\nFAILED\n");
  } else {
    printf("\nOK\n");
  }
}

void test2(void) {
  word_t pre[NARGS] = { 0, 4294967295, 4294967295, 4294967293, 0, 0, 4294967293, 0, 0 };
  word_t post[NARGS];

  assert(well_formed(pre));
  update(pre, post, x, y);

  print_heap(pre);
  printf("x->n = y\n");
  print_heap(post);

  if (!well_formed(post)) {
    printf("\nFAILED\n");
  } else {
    printf("\nOK\n");
  }
}

void test3(void) {
  word_t pre[NARGS] = { 0, 3, 0, 4294967295, 0, 4294967295, 0, 3, 0 };
  word_t post[NARGS];

  assert(well_formed(pre));
  lookup(pre, post, x, y);

  print_heap(pre);
  printf("x = y->n\n");
  print_heap(post);

  assert(well_formed(post));
}

int main(void) {
  printf("\ntest1\n");
  test1();

  printf("\ntest2\n");
  test2();
}
