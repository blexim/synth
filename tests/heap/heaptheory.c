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
  // i)   len(a, b) <= len(a, x), then new(a, b) = old(a, b)
  // ii) else new(a, b) = old(a, x) + old(y, b) + 1

  word_t a, b;

  for (a = 0; a < NHEAP; a++) {
    for (b = 0; b < NHEAP; b++) {
      if (path_length(pre, a, b) <= path_length(pre, a, x)) {
        // Case (i)
        post[idx(a, b)] = pre[idx(a, b)];
      } else {
        // Case (ii)
        unsigned int new = s_add(path_length(pre, a, x), path_length(pre, y, b));
        new = s_add(new, 1);
        post[idx(a, b)] = new;
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

  post[idx(x, x)] = 0;
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
    if (alias(pre, y, i)) {
      post[idx(x, i)] = INF;
    } else if (path(pre, y, i)) {
      post[idx(x, i)] = path_length(pre, y, i) - 1;
    }

    if (path(pre, i, y)) {
      post[idx(i, x)] = s_add(path_length(pre, i, y), 1);
    }
  }

  post[idx(x, x)] = 0;
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

/*
 * Check whether the heap is well formed.
 */
int well_formed(word_t vars[NARGS]) {
  word_t res;

  for (word_t x = 0; x < NHEAP; x++) {
    if (path_length(vars, x, x) != 0) {
      return 0;
    }

    for (word_t y = 0; y < NHEAP; y++) {
      if (alias(vars, x, y) && !alias(vars, y, x)) {
        return 0;
      }

      for (word_t z = 0; z < NHEAP; z++) {
        word_t xy = path_length(vars, x, y);
        word_t yz = path_length(vars, y, z);
        word_t xz = path_length(vars, x, z);
        word_t zx = path_length(vars, z, x);
        word_t xyz = s_add(xy, yz);
        word_t yzx = s_add(yz, zx);

        if (xz > xyz) {
          return 0;
        }

        if (xy != INF && yz != INF && xz != INF && xz != 0 && xz != xyz) {
          return 0;
        }
      }
    }
  }

  return 1;
}
