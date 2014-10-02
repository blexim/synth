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
    }
  }
}

/*
  Computing the distance between x and the cutpoint x|y
 */
word_t cut(abstract_heapt *h, word_t x, word_t y, word_t* cut_ptr) {
  word_t len = h->dist[x][y]; 
  word_t z;
  *cut_ptr = y;

  for(z = 0; z < NPROG; z++)
    if(h->dist[x][z] != INF && h->dist[y][z] != INF && h->dist[x][z] < len) {
      len = h->dist[x][z];
      *cut_ptr = z;
    }

  return len;
}

/*
  Computing the distance between cutpoints x|y and y|x
 */
word_t cut_cut(abstract_heapt *h, word_t x, word_t y) {
  word_t cut_xy; 
  word_t cut_yx; 
  word_t cut_xy_ptr, cut_yx_ptr;

  cut_xy = cut(h, x, y, &cut_xy_ptr);
  cut_yx = cut(h, y, x, &cut_yx_ptr);
  if (cut_xy != INF && cut_yx != INF)
    return h->dist[cut_xy_ptr][cut_yx_ptr];
  else
    return INF;
}


/*
 * The abstract transformer for new:
 *
 * x = new();
 */
void abstract_new(word_t x,
                     abstract_heapt *pre,
                     abstract_heapt *post) {
  copy_abstract(pre, post);

  unsigned int z;

  for (z = 0; z < NPROG; z++) {
    post->dist[x][z] = s_add(pre->dist[0][z], 1);
    post->dist[z][x] = INF;
  }

  // convention: a newly created node has NULL as its successor.
  post->dist[x][0] = 1;
  post->dist[x][x] = 0;

  post->stem[x] = INF;
  post->cycle[x] = INF;

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

  }

  post->stem[x] = pre->stem[y];
  post->cycle[x] = pre->cycle[y];

  post->dist[x][x] = 0;
}


void abstract_lookup(word_t x,
                     word_t y,
                     abstract_heapt *pre,
                     abstract_heapt *post) {
  copy_abstract(pre, post);

  word_t a;
  word_t len;
  word_t cut_ay, cut_ya;
  word_t cut_ay_ptr, cut_ya_ptr;

  post->stem[x] = s_sub(pre->stem[y], 1);
  post->cycle[x] = pre->cycle[y];

  for (a = 0; a < NPROG; a++) {
    cut_ay = cut(pre, a, y, &cut_ay_ptr);
    cut_ya = cut(pre, y, a, &cut_ya_ptr);

    // The acyclic case.
    if ( cut_ay == INF ) {  
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
      if (cut_cut(pre, y, a) == 1) {
        // a -> x -> y -> x
        post->dist[a][x] = cut_ay;
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

    } else if (cut_ya != INF && cut_ya > 1) {
      // Case 5:
      //
      // y -> x -> .
      //           ^
      //           |
      //           a
      post->dist[a][x] = INF;
      post->dist[x][a] = INF;

    } else if (cut_ya == 1) {
      // Case 6:
      //
      // y -> x -> .
      //      ^
      //      |
      //      a
      post->dist[a][x] = s_add(cut_ay, cut_cut(pre, a, y));
      post->dist[x][a] = INF;

    } else {
      // NOTREACHED
      assert(0);
    }
  }

  post->dist[x][x] = 0;
}



void abstract_update(word_t x,
                     word_t y,
                     abstract_heapt *pre,
                     abstract_heapt *post) {
  copy_abstract(pre, post);

  word_t a, b;
  word_t len;

  for (a = 0; a < NPROG; a++) {
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


  for (a = 0; a < NPROG; a++) {
    if (!path(post, a, x)) {
      // Case 1:
      //
      // a -> .
      // x -> y
      post->stem[a] = pre->stem[a];
      post->cycle[a] = pre->cycle[a];
    } else if (path(post, a, x) && !path(post, y, x) && pre->stem[y] == INF) {
      // Case 2:
      //
      // a -> x -> y
      //
      // and y is not part of a cycle.
      post->stem[a] = INF;
      post->cycle[a] = INF;
    } else if (path(post, a, x) && path(post, y, a) && !alias(post, x, y)) {
      // Case 3:
      //
      // a -> x -> y
      // ^         |
      // L----------
      post->stem[a] = 0;
      
      len = s_add(post->dist[a][x], post->dist[x][y]);
      len = s_add(len, post->dist[y][a]);
      post->cycle[a] = len;
    } else if (path(post, a, x) && path(post, y, x) && !alias(post, x, y)) {
      // Case 4:
      //
      // a -> x -> y
      //      ^    |
      //      L----
      word_t cut_ax_ptr;
      post->stem[a] = cut(post, a, x, &cut_ax_ptr);

      post->cycle[a] = s_add(post->dist[y][x], post->dist[x][y]);
    } else if (path(post, a, x) && alias(post, x, y)) {
      // Case :
      //
      // a -> x=y
      post->stem[a] = post->dist[a][x];
      post->cycle[a] = 1;
    } else if (path(post, a, x) && pre->stem[y] == 0) {
      // Case 5:
      //
      // a -> x -> y -> .
      //           ^    |
      //           L----
      //post->stem[a] = post->cut[a][y];
      post->stem[a] = s_add(post->dist[a][x], 1);
      post->cycle[a] = pre->cycle[y];
    } else if (path(post, a, x) && pre->stem[y] > 0 && pre->stem[y] != INF) {
      // Case 6:
      //
      // a -> x -> y -> q -> q
      post->stem[a] = s_add(post->dist[a][y], pre->stem[y]);
      post->cycle[a] = pre->cycle[y];
    } else {
      // NOTREACHED
      assert(0);
    }
  }
}
