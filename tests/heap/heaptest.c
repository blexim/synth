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
        printf("%-14s", "INF");
      } else {
        printf("0x%-12x", ab);
      }
    }

    printf("\n");
  }
}

void test_update(word_t pre[NARGS]) {
  word_t post[NARGS];

  update(pre, post, x, y);

  print_heap(pre);
  printf("Well formed: %s\n", well_formed(pre) ? "yes" : "no");
  printf("x->n = y\n");
  print_heap(post);
  printf("Well formed: %s\n", well_formed(post) ? "yes" : "no");

  if (well_formed(pre) && !well_formed(post)) {
    printf("\nFAILED\n");
  } else {
    printf("\nOK\n");
  }
}

#define NUPDATE 3
word_t update_tests[NUPDATE][NARGS] = {
  { 0, 2147483648, 4294967295, 4294967295, 0, 4294967295, 4294967295, 4294967295, 0 },
  { 0, 4294967295, 4294967295, 4294967293, 0, 0, 4294967293, 0, 0 },
  { 0, 805306368, 4294967295, 402702336, 0, 3791650816, 4294967295, 4127178237, 0 }
};


void test_lookup(word_t pre[NARGS]) {
  word_t post[NARGS];

  lookup(pre, post, x, y);

  print_heap(pre);
  printf("Well formed: %s\n", well_formed(pre) ? "yes" : "no");
  printf("x = y->n\n");
  print_heap(post);
  printf("Well formed: %s\n", well_formed(post) ? "yes" : "no");

  if (well_formed(pre) && !well_formed(post)) {
    printf("\nFAILED\n");
  } else {
    printf("\nOK\n");
  }
}

#define NLOOKUP 3
word_t lookup_tests[NLOOKUP][NARGS] = {
  { 0, 4294967295, 4294967295, 4286578687, 0, 8388608, 4278190079, 4294967295, 0 },
  { 0, 0, 1213072394, 0, 0, 1213072394, 1037839350, 1037839350, 0 },
  { 0, 4294967295, 4026531839, 4294967295, 0, 4294967295, 16777216, 4294967295, 0 },
};

int main(void) {
  int i;

  printf("Testing update:\n");
  for (i = 0; i < NUPDATE; i++) {
    printf("\nTest %d:\n", i);
    test_update(update_tests[i]);
  }

  printf("\nTesting lookup:\n");
  for (i = 0; i < NLOOKUP; i++) {
    printf("\nTest %d:\n", i);
    test_lookup(lookup_tests[i]);
  }
}
