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
 * Is there a path a->b?
 */
int path(abstract_heapt *heap,
         word_t a,
         word_t b) {
  return heap->dist[a][b] != INF;
}

/*
 * Does a cut b?
 */
int cut(abstract_heapt *heap,
        word_t a,
        word_t b) {
  return heap->cut[a][b] != INF;
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

  post->stem[x] = s_sub(pre->stem[y], 1);
  post->cycle[x] = pre->cycle[y];

  for (a = 0; a < NPROG; a++) {
    //__CPROVER_assume(pre->stem[y] > 1);
    // The acyclic case.
    if (!cut(pre, a, y)) {
      // Case 1:
      //
      // a -> .
      // y -> x -> .
      post->dist[a][x] = INF;
      post->dist[x][a] = INF;
    } else if (pre->dist[y][a] == 1) {
      // Case 4:
      //
      // y -> a=x
      post->dist[a][x] = 0;
      post->dist[x][a] = 0;
    } else if (path(pre, a, y) && pre->stem[y] > 0) {
      // Case 2:
      //
      // a -> y -> x
      // OR
      // a = y -> x
      //
      // AND
      //
      // y is not in a cycle
      post->dist[a][x] = s_add(pre->dist[a][y], 1);
      post->dist[x][a] = INF;
    } else if (path(pre, a, y) && pre->stem[y] == 0 && pre->stem[a] > 0 && pre->cycle[y] > 1) {
      // Case 2x:
      //
      // a -> y -> x -> y
      //
      // a is not in a cycle
      if (pre->cut_cut[y][a] == 1) {
        // a -> x -> y -> x
        post->dist[a][x] = pre->cut[a][y];
      } else {
        post->dist[a][x] = s_add(pre->dist[a][y], 1);
      }

      post->dist[x][a] = INF;
    } else if (path(pre, a, y) && pre->stem[y] == 0 && pre->stem[a] > 0 && pre->cycle[y] == 1) {
      // Case 2xx:
      //
      // a -> y=x -> y=x
      post->dist[a][x] = pre->dist[a][y];
      post->dist[x][a] = INF;
    } else if (path(pre, a, y) && pre->stem[a] == 0 && pre->cycle[a] > 1 && pre->dist[a][y] == 0) {
      // Case 2a:
      //
      // a=y -> x -> a=y
      //
      // Note: stem[a] = 0 ==> stem[y] = 0
      len = s_sub(pre->cycle[a], 1);
      post->dist[a][x] = 1;
      post->dist[x][a] = len;
    } else if (path(pre, a, y) && pre->stem[a] == 0 && pre->cycle[a] > 1 && pre->dist[a][y] > 0) {
      // Case 2b:
      //
      // a -> y -> x -> a
      len = s_add(pre->dist[a][y], 1);
      post->dist[a][x] = len;

      len = s_sub(pre->cycle[a], len);
      post->dist[x][a] = len;
    } else if (path(pre, a, y) && pre->stem[a] == 0 && pre->cycle[a] == 1) {
      // Case 2b:
      //
      // a=y -> x=y=a
      assert(post->dist[a][y] == 0 && post->dist[y][a] == 0);
      post->dist[a][x] = 0;
      post->dist[x][a] = 0;
    } else if (path(pre, y, a) && pre->dist[y][a] > 1 && pre->stem[y] > 1) {
      // Case 3:
      //
      // y -> x -> a
      // 
      // AND
      //
      // x is not in a cycle
      post->dist[a][x] = INF;
      post->dist[x][a] = s_sub(pre->dist[y][a], 1);
    } else if (path(pre, y, a) && pre->dist[y][a] > 1 && pre->stem[y] == 1) {
      // Case 3a:
      //
      // y -> x -> a -> x
      assert(pre->stem[a] == 0 && pre->cycle[a] > 0);

      len = s_sub(pre->dist[y][a], 1);
      post->dist[x][a] = len;

      len = s_sub(pre->cycle[a], len);
      post->dist[a][x] = len;
    } else if (cut(pre, y, a) && pre->cut[y][a] > 1) {
      // Case 5:
      //
      // y -> x -> .
      //           ^
      //           |
      //           a
      post->dist[a][x] = INF;
      post->dist[x][a] = INF;
    } else if (pre->cut[y][a] == 1) {
      // Case 6:
      //
      // y -> x -> .
      //      ^
      //      |
      //      a
      post->dist[a][x] = s_add(pre->cut[a][y], pre->cut_cut[a][y]);
      post->dist[x][a] = INF;
    } else {
      // NOTREACHED
      assert(0);
    }
  }

  post->dist[x][x] = 0;
}
