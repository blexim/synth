#include <stdio.h>
#include <assert.h>

#include "heaptheory.h"
#include "synth.h"

#define x 0
#define y 1
#define z 2

void print_heap(word_t vars[NARGS]) {
  int a, b;
  char sep[] = "  |  ";

  printf("%-14s", "Paths");

  for (a = 1; a < NHEAP; a++) {
    printf("%14s", "");
  }

  printf("%sCuts\n", sep);

  for (a = 0; a < NHEAP; a++) {
    for (b = 0; b < NHEAP; b++) {
      unsigned int ab = path_length(vars, a, b);

      if (ab == INF) {
        printf("%-14s", "INF");
      } else {
        printf("%#-14x", ab);
      }
    }

    printf("%s", sep);

    for (b = 0; b < NHEAP; b++) {
      unsigned int ab = cut_length(vars, a, b);

      if (ab == INF) {
        printf("%-14s", "INF");
      } else {
        printf("%#-14x", ab);
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

#define NUPDATE 0
word_t update_tests[NUPDATE][NARGS] = {
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

#define NLOOKUP 4
word_t lookup_tests[NLOOKUP][NARGS] = {
  { 0, 0, 1, INF, 0, 0, 1, INF, INF, INF, 0, INF, INF, INF, 1, 0,
    0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0 },
  { 0, 536870913, 4294967295, 536870911, 4294967294, 0, 4294967293, 4294967295, 1, 536870914, 0, 536870912, 4294967295, 2, 4294967295, 0, 0, 0, 0, 536870911, 0, 0, 0, 0, 1, 0, 0, 536870912, 0, 2, 0, 0 },
  { 0, INF, INF, 0x100, 4, 0, 0, 0x104, 4, 0, 0, 0x104, 0x200, INF, INF, 0, 0, 0, 0, 0, 4, 0, 0, 0x104, 4, 0, 0, 0x104, 0, 0, 0, 0 },
  { 0, 65010287, 2382364671, 2281701375, 3927967120, 0, 2317354384, 2216691088, 1610612736, 1675623023, 0, 3892314111, 1711276032, 1776286319, 100663296, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 },
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
