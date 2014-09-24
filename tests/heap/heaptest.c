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
  word_t pre[NARGS] = {  0, 805306368, 4294967295, 402702336, 0, 3791650816, 4294967295, 4127178237, 0 };
  word_t post[NARGS];

  //assert(well_formed(pre));
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

void test4(void) {
  word_t pre[NARGS] = {    0, 4294967295, 4294967295, 4286578687, 0, 8388608, 4278190079, 4294967295, 0 };
  word_t post[NARGS];

  assert(well_formed(pre));
  lookup(pre, post, x, y);

  print_heap(pre);
  printf("x = y->n\n");
  print_heap(post);

  if (!well_formed(post)) {
    printf("\nFAILED\n");
  } else {
    printf("\nOK\n");
  }
}
void test5(void) {
  word_t pre[NARGS] = {    0, 0, 1213072394, 0, 0, 1213072394, 1037839350, 1037839350, 0 };
  word_t post[NARGS];

  assert(well_formed(pre));
  lookup(pre, post, x, y);

  print_heap(pre);
  printf("x = y->n\n");
  print_heap(post);

  if (!well_formed(post)) {
    printf("\nFAILED\n");
  } else {
    printf("\nOK\n");
  }
}

int main(void) {
  printf("\ntest1\n");
  test1();

  printf("\ntest2\n");
  test2();

  printf("\ntest3\n");
  test3();

  printf("\ntest4\n");
  test4();

  printf("\ntest5\n");
  test5();
}
