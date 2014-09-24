#include "synth.h"
#include "heaptheory.h"

#ifdef SEARCH
 #define __CPROVER_assume(x)
#endif

/*
 * Saturating addition.
 */
unsigned int s_add(unsigned int x, unsigned int y) {
  unsigned int ret = (x > INF - y) ? INF : x + y;

  __CPROVER_assume(ret != INF || x == INF || y == INF);

  return ret;
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
  //       This is the case where x does not appear between a and b, so the
  //       update does not change the reachability.
  // ii)  len(y, b) < len(y, x), then new(a, b) = old(a, x) + old(y, b) + 1
  //       This is the case where x _does_ appear between a and b, but the
  //       path y -> b did not go through x (i.e. there is no cycle x -> y -> x),
  //       so we can just stitch the two paths together.
  // iii) else new(a, b) = INF
  //       This is the case where x was in the path a -> b, but there is no
  //       path y -> b that does not include x, so b is no longer reachable
  //       from a.

  word_t a, b;

  for (a = 0; a < NHEAP; a++) {
    for (b = 0; b < NHEAP; b++) {
      if (path_length(pre, a, b) <= path_length(pre, a, x)) {
        // Case (i)
        post[idx(a, b)] = pre[idx(a, b)];
      } else if (path_length(pre, y, b) <= path_length(pre, y, x)) {
        // Case (ii)
        unsigned int new = s_add(path_length(pre, a, x), path_length(pre, y, b));
        new = s_add(new, 1);
        post[idx(a, b)] = new;
      } else {
        // Case (iii)
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

  unsigned int cycle = cycle_length(pre, y);

  for (i = 0; i < NHEAP; i++) {
    if (alias(pre, y, i)) {
      if (cycle == INF) {
        post[idx(x, i)] = INF;
      } else {
        post[idx(x, i)] = cycle - 1;
      }
    } else if (path(pre, y, i)) {
      post[idx(x, i)] = path_length(pre, y, i) - 1;
    } else {
      post[idx(x, i)] = INF;
    }

    if (path(pre, i, y) || path(pre, i, x)) {
      post[idx(i, x)] = s_add(path_length(pre, i, y), 1);
   }

    if (path_length(pre, y, i) == 1) {
      post[idx(i, x)] = 0;
    }
  }

  post[idx(x, x)] = 0;
}

/*
 * Find the length of the cyclic path connection x -*> x.
 */
unsigned int cycle_length(word_t vars[NARGS], word_t x) {
  int i;

  for (i = 0; i < NHEAP; i++) {
    unsigned int xi = path_length(vars, x, i);
    unsigned int ix = path_length(vars, i, x);

    if (xi != 0 && xi != INF && ix != INF) {
      return s_add(xi, ix);
    }
  }

  return INF;
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
  for (word_t x = 0; x < NHEAP; x++) {
    if (path_length(vars, x, x) != 0) {
      return 0;
    }

    for (word_t y = 0; y < NHEAP; y++) {
      if (alias(vars, x, y) && !alias(vars, y, x)) {
        return 0;
      }

      for (word_t z = 0; z < NHEAP; z++) {
        unsigned int xy = path_length(vars, x, y);
        unsigned int xz = path_length(vars, x, z);
        unsigned int yx = path_length(vars, y, x);
        unsigned int yz = path_length(vars, y, z);
        unsigned int zx = path_length(vars, z, x);
        unsigned int zy = path_length(vars, z, y);

        unsigned int xyz = s_add(xy, yz);
        unsigned int xzy = s_add(xz, zy);

        if (xz != xyz && xy != xzy) {
          return 0;
        }

        /*
        if (path(vars, x, z) && path(vars, y, z) && path(vars, z, y)) {
          if (xz != xyz && xy != xzy) {
            return 0;
          }
        } else if (path(vars, x, y) && path(vars, y, z)) {
          if (xz != xyz) {
            return 0;
          }
        }

        if (path(vars, x, y) && path(vars, x, z)) {
          if (xz != xyz && xy != xzy) {
            return 0;
          }
        }

        if (path(vars, x, y) && path(vars, x, z) &&
            path(vars, y, z) && path(vars, z, y) &&
            !path(vars, z, x) && !path(vars, y, x)) {
          // There is a cycle between y and z, and x leads into one of those
          // from the outside...
          if (xz != xyz && xy != xzy) {
            return 0;
          }
        }

        if (path(vars, x, y) &&
            path(vars, y, z) &&
            path(vars, z, x)) {
          // x, y, z are in a cycle...
          if (xz != xyz && xy != xzy) {
            return 0;
          }
        }
        */
      }
    }
  }

  return 1;
}
