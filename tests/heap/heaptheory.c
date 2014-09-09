#include "synth.h"
#include "heaptheory.h"

/*
 * Saturating addition.
 */
unsigned int s_add(unsigned int x, unsigned int y) {
  return (x > INF - y) ? INF : x + y;
}

/*
 * Return the length of the shortest path from x to y.
 */
unsigned int path_length(word_t args[NARGS], word_t x, word_t y) {
  word_t ret = args[idx(x, y)];

  //SIGN_EXTEND(ret);

  return ret;
}

/*
 * Is there a path from x to y?
 */
int path(word_t args[NARGS], word_t x, word_t y) {
  return path_length(args, x, y) != INF;
}

/*
 * Is there a path from x to z, and if so is y on it?
 */
int onpath(word_t args[NARGS], word_t x, word_t y, word_t z) {
  int xz = path_length(args, x, z);
  int xy = path_length(args, x, y);

  return (xz > 0 && xy > 0 && xy < xz);
}

/*
 * Do x and y alias?
 */
int alias(word_t args[NARGS], word_t x, word_t y) {
  return path_length(args, x, y) == 0;
}

/*
 * Update the heap with the statement:
 *
 * x->n = y;
 */
int update(word_t pre[NARGS], word_t post[NARGS], word_t x, word_t y) {
  // First copy the stack.
  int i;

  for (i = 0; i < NSTACK; i++) {
    post[i] = pre[i];
  }

  // Now update the heap by applying the following rules:
  // 
  // For each pair (a, b) in the old heap, in the new heap:
  //
  // i)    a -*> b && !x -> b, then new(a, b) = old(a, b)
  // ii)    a -*> b && x == b, then new(a, b) = old(a, b)
  // iii)   a -*> x && y -*> b, then new(a, b) = min(old(a, b), old(a, x) + old(y, b) + 1)
  // iv)  else new(a, b) = infinity

  word_t a, b;

  for (a = 0; a < NHEAP; a++) {
    for (b = 0; b < NHEAP; b++) {
      if (path(pre, a, b) && !path(pre, x, b)) {
        // Case (i)
        post[idx(a, b)] = pre[idx(a, b)];
      } else if (path(pre, a, b) && alias(pre, x, b)) {
        // Case (ii)
        post[idx(a, b)] = pre[idx(a, b)];
      } else if (path(pre, a, x) && path(pre, y, b)) {
        // Case (iii)
        unsigned int old = path_length(pre, a, b);
        unsigned int new = s_add(path_length(pre, a, x), path_length(pre, y, b));
        new = s_add(new, 1);

        post[idx(a, b)] = min(old, new);
      } else {
        // Case (iv)
        post[idx(a, b)] = INF;
      }
    }
  }
}

/*
 * Do the pointer assignment x = y
 */
int assign(word_t pre[NARGS], word_t post[NARGS], word_t x, word_t y) {
  int i;

  for (i = 0; i < NARGS; i++) {
    post[i] = pre[i];
  }

  for (i = 0; i < NHEAP; i++) {
    post[idx(x, i)] = pre[idx(y, i)];
    post[idx(i, x)] = pre[idx(i, y)];
  }
}

/*
 * Do the pointer assignment x = y->n
 */
int lookup(word_t pre[NARGS], word_t post[NARGS], word_t x, word_t y) {
  int i;

  for (i = 0; i < NARGS; i++) {
    post[i] = pre[i];
  }

  for (i = 0; i < NHEAP; i++) {
    if (path(pre, y, i)) {
      post[idx(x, i)] = path_length(pre, y, i) - 1;
    }

    if (path(pre, i, y)) {
      post[idx(i, x)] = s_add(path_length(pre, i, y), 1);
    }
  }
}

/*
 * Allocate a new cell:
 *
 * x = new()
 */
void alloc(word_t pre[NARGS], word_t post[NARGS], word_t x) {
  int i;

  for (i = 0; i < NARGS; i++) {
    post[i] = pre[i];
  }

  for (i = 0; i < NHEAP; i++) {
    post[idx(x, i)] = INF;
    post[idx(i, x)] = INF;
  }

  post[idx(x, x)] = 0;
}
