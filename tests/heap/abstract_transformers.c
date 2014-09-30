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
 * Does a alias b?
 */
int alias(abstract_heapt *heap,
          word_t a,
          word_t b) {
  return heap->dist[a][b] == 0;
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
    // The acyclic case.
    if (!cut(pre, a, y)) {
      // Case 1:
      //
      // a -> .
      // y -> x -> .
      post->dist[a][x] = INF;
      post->dist[x][a] = INF;

      post->cut[a][x] = INF;
      post->cut[x][a] = INF;

      post->cut_cut[a][x] = INF;
      post->cut_cut[x][a] = INF;
    } else if (pre->dist[y][a] == 1) {
      // Case 4:
      //
      // y -> a=x
      post->dist[a][x] = 0;
      post->dist[x][a] = 0;

      post->cut[a][x] = 0;
      post->cut[x][a] = 0;

      post->cut_cut[a][x] = 0;
      post->cut_cut[x][a] = 0;
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

      post->cut[a][x] = post->dist[a][x];
      post->cut[x][a] = 0;

      post->cut_cut[a][x] = 0;
      post->cut_cut[x][a] = 0;
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

      post->cut[a][x] = pre->cut[a][y];
      post->cut[x][a] = 0;

      if (post->dist[a][x] == post->cut[a][x]) {
        post->cut_cut[a][x] = 0;
        post->cut_cut[x][a] = 0;
      } else {
        post->cut_cut[a][x] = s_sub(post->dist[a][x], post->cut[a][x]);
        post->cut_cut[x][a] = s_sub(post->cycle[x], post->cut_cut[a][x]);
      }
    } else if (path(pre, a, y) && pre->stem[y] == 0 && pre->stem[a] > 0 && pre->cycle[y] == 1) {
      // Case 2xx:
      //
      // a -> y=x -> y=x
      post->dist[a][x] = pre->dist[a][y];
      post->dist[x][a] = INF;

      post->cut[a][x] = post->dist[a][x];
      post->cut[x][a] = 0;

      post->cut_cut[a][x] = 0;
      post->cut_cut[x][a] = 0;
    } else if (path(pre, a, y) && pre->stem[a] == 0 && pre->cycle[a] > 1 && pre->dist[a][y] == 0) {
      // Case 2a:
      //
      // a=y -> x -> a=y
      //
      // Note: stem[a] = 0 ==> stem[y] = 0
      len = s_sub(pre->cycle[a], 1);
      post->dist[a][x] = 1;
      post->dist[x][a] = len;

      post->cut[a][x] = 0;
      post->cut[x][a] = 0;

      post->cut_cut[a][x] = 1;
      post->cut_cut[x][a] = len;
    } else if (path(pre, a, y) && pre->stem[a] == 0 && pre->cycle[a] > 1 && pre->dist[a][y] > 0) {
      // Case 2b:
      //
      // a -> y -> x -> a
      len = s_add(pre->dist[a][y], 1);
      post->dist[a][x] = len;

      len = s_sub(pre->cycle[a], len);
      post->dist[x][a] = len;

      post->cut[a][x] = 0;
      post->cut[x][a] = 0;

      post->cut_cut[a][x] = post->dist[a][x];
      post->cut_cut[x][a] = post->dist[x][a];
    } else if (path(pre, a, y) && pre->stem[a] == 0 && pre->cycle[a] == 1) {
      // Case 2b:
      //
      // a=y -> x=y=a
      assert(post->dist[a][y] == 0 && post->dist[y][a] == 0);
      post->dist[a][x] = 0;
      post->dist[x][a] = 0;

      post->cut[a][x] = 0;
      post->cut[x][a] = 0;

      post->cut_cut[a][x] = 0;
      post->cut_cut[x][a] = 0;
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

      post->cut[a][x] = 0;
      post->cut[x][a] = s_sub(pre->cut[y][a], 1);

      post->cut_cut[a][x] = pre->cut_cut[a][y];
      post->cut_cut[x][a] = pre->cut_cut[y][a];
    } else if (path(pre, y, a) && pre->dist[y][a] > 1 && pre->stem[y] == 1) {
      // Case 3a:
      //
      // y -> x -> a -> x
      assert(pre->stem[a] == 0 && pre->cycle[a] > 0);

      len = s_sub(pre->dist[y][a], 1);
      post->dist[x][a] = len;

      len = s_sub(pre->cycle[a], len);
      post->dist[a][x] = len;

      post->cut[a][x] = 0;
      post->cut[x][a] = 0;

      post->cut_cut[a][x] = post->dist[a][x];
      post->cut_cut[x][a] = post->dist[x][a];
    } else if (cut(pre, y, a) && pre->cut[y][a] > 1) {
      // Case 5:
      //
      // y -> x -> .
      //           ^
      //           |
      //           a
      post->dist[a][x] = INF;
      post->dist[x][a] = INF;

      post->cut[a][x] = pre->cut[a][y];
      post->cut[x][a] = s_sub(pre->cut[y][a], 1);

      post->cut_cut[a][x] = pre->cut_cut[a][y];
      post->cut_cut[x][a] = pre->cut_cut[y][a];
    } else if (pre->cut[y][a] == 1) {
      // Case 6:
      //
      // y -> x -> .
      //      ^
      //      |
      //      a
      post->dist[a][x] = s_add(pre->cut[a][y], pre->cut_cut[a][y]);
      post->dist[x][a] = INF;

      post->cut[a][x] = pre->cut[a][y];
      post->cut[x][a] = 0;

      post->cut_cut[a][x] = pre->cut_cut[a][y];
      post->cut_cut[x][a] = pre->cut_cut[y][a];
    } else {
      // NOTREACHED
      assert(0);
    }
  }

  post->dist[x][x] = 0;
  post->cut[x][x] = 0;
  post->cut_cut[x][x] = 0;
}

void abstract_update(word_t x,
                     word_t y,
                     abstract_heapt *pre,
                     abstract_heapt *post) {
  copy_abstract(pre, post);

  word_t a, b;
  word_t len;

  for (a = 0; a < NPROG; a++) {
    // Cycles!
    if (!path(pre, a, x)) {
      // Case 1:
      //
      // a -> .
      // x -> .
      post->stem[a] = pre->stem[a];
      post->cycle[a] = pre->cycle[a];
    } else if (path(pre, a, x) && !path(pre, y, x) && pre->stem[y] == INF) {
      // Case 2:
      //
      // a -> x ~> y -> .
      post->stem[a] = INF;
      post->cycle[a] = INF;
    } else if (path(pre, a, x) && !path(pre, y, x) && pre->stem[y] != INF) {
      // Case 3:
      //
      // a -> x ~> y -> q -> q
      len = s_add(pre->dist[a][x], pre->stem[y]);
      len = s_add(len, 1);
      post->stem[a] = len;
      post->cycle[a] = pre->cycle[y];
    } else if (path(pre, a, x) && path(pre, y, x) && !path(pre, y, a)) {
      // Case 4:
      //
      // a -> x ~> y
      //      ^    |
      //      |    v
      //      L--- .
      post->stem[a] = pre->cut[a][y];
      post->cycle[a] = s_add(pre->dist[y][x], 1);
    } else if (path(pre, a, x) && path(pre, y, a) && !alias(pre, x, y)) {
      // Case 5:
      //
      // a -> x ~> y
      // ^         |
      // |         v
      // L-------- .
      post->stem[a] = 0;

      len = s_add(pre->dist[y][a], pre->dist[a][x]);
      len = s_add(len, 1);
      post->cycle[a] = len;
    } else if (path(pre, a, x) && path(pre, y, a) && alias(pre, x, y) && !alias(pre, x, a)) {
      // Case 6:
      //
      // a -> x=y
      // ^      |
      // |-------
      post->stem[a] = pre->dist[a][x];
      post->cycle[a] = 1;
    } else if (alias(pre, a, x) && alias(pre, a, y)) {
      // Case 7:
      //
      // a=x=y
      post->stem[a] = 0;
      post->cycle[a] = 1;
    } else {
      // NOTREACHED
      assert(0);
    }

    for (b = 0; b < NPROG; b++) {
      if (pre->dist[a][b] <= pre->dist[a][x]) {
        // Case 1:
        //
        // a -> b
        // x -> y
        post->dist[a][b] = pre->dist[a][b];
      } else if (pre->dist[y][b] < pre->dist[y][x]) {
        len = s_add(pre->dist[a][x], pre->dist[y][b]);
        len = s_add(len, 1);
        post->dist[a][b] = len;
      } else {
        post->dist[a][b] = INF;
      }
    }
  }
}
