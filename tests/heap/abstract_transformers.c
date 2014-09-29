#include "heapabstract.h"

/*
 * Saturating addition.
 */
unsigned int s_add(unsigned int x, unsigned int y) {
  unsigned int ret = (x > INF - y) ? INF : x + y;

  __CPROVER_assume(ret != INF || x == INF || y == INF);

  return ret;
}

/*
 * Saturating subtraction.
 */
unsigned int s_sub(unsigned int x, unsigned int y) {
  if (x == INF) {
    return INF;
  } else if (y > x) {
    return 0;
  } else {
    return x - y;
  }
}

/*
 * Copy an abstract heap.
 */
void copy_abstract(abstract_heapt *pre,
                   abstract_heapt *post) {
  word_t x, y;

  for (x = 0; x < NPROG; x++) {
    post->stem[x] = pre->stem[x];
    post->cycle[x] = pre->cycle[x];

    for (y = 0; y < NPROG; y++) {
      post->dist[x][y] = pre->dist[x][y];
      post->cut[x][y] = pre->cut[x][y];
      post->cut_cut[x][y] = pre->cut_cut[x][y];
    }
  }
}

/*
 * The abstract transformer for assignment:
 *
 * x = y;
 */
void abstract_assign(word_t x,
                     word_t y,
                     abstract_heapt *pre,
                     abstract_heapt *post) {
  copy_abstract(pre, post);

  unsigned int z;

  for (z = 0; z < NPROG; z++) {
    post->dist[x][z] = pre->dist[y][z];
    post->dist[z][x] = pre->dist[z][y];

    post->cut[x][z] = pre->cut[y][z];
    post->cut[z][x] = pre->cut[z][y];

    post->cut_cut[x][z] = pre->cut_cut[y][z];
    post->cut_cut[z][x] = pre->cut_cut[z][y];
  }

  post->stem[x] = pre->stem[y];
  post->cycle[x] = pre->cycle[y];

  post->dist[x][x] = 0;
  post->cut[x][x] = 0;
  post->cut_cut[x][x] = 0;
}

void abstract_lookup(word_t x,
                     word_t y,
                     abstract_heapt *pre,
                     abstract_heapt *post) {
  copy_abstract(pre, post);

  word_t a;
  word_t len;

  for (a = 0; a < NPROG; a++) {
    // First we work out the distance x -> a
    if (a == x) {
      // a == x, and x always aliases itself.
      post->dist[x][a] = 0;
    } else if (pre->dist[a][y] == 0) {
      // a is an alias of y...
      if (pre->stem[y] == 0) {
        // y is part of a cycle of length k, so x -> a == x -> y == k-1
        post->dist[x][a] = s_sub(pre->cycle[y], 1);
      } else {
        // y cannot reach y, and so x cannot.
        post->dist[x][a] = INF;
      }
    } else {
      // Otherwise, the distance y -> a is k, and so x -> a = k-1
      post->dist[x][a] = s_sub(pre->dist[y][a], 1);
    }

    // Now work out the distance a -> x
    if (a == x) {
      post->dist[x][a] = 0;
    } else if (pre->cut[y][a] == 1 && pre->dist[y][a] == INF) {
      // y is one step away from a cutpoint with a.  There is a bit of trickery
      // here -- we have to remember to account for the distance between the ay
      // cutpoint and the ya cutpoint.
      post->dist[a][x] = s_add(pre->cut[a][y], pre->cut_cut[a][y]);
    } else if (pre->cut[y][a] == 1 && pre->cycle[a] != INF) {
      // y is one step away from a cycle containing a.
      len = s_sub(pre->cycle[a], pre->dist[y][a]);
      len = s_add(len, 1);
      post->dist[a][x] = len;
    } else if (pre->dist[y][a] == 1) {
      post->dist[a][x] = 0;
    } else {
      // Otherwise, the distance a -> y is k, so a -> x = k+1
      post->dist[a][x] = s_add(pre->dist[a][y], 1);
    }
  }
}
