#include <stdio.h>
#include <assert.h>

#ifndef NNODES
 #define NNODES 5
#endif

#define NMATRIX (NNODES + NPROG)

#ifndef NPROG
 #define NPROG (NNODES/2)
#endif

#define ABSSIZE (NPROG*NPROG*3 + NPROG*2)

#define INF 0xffffffff

#define idx(x, y) (x*NNODES + y)
#define ptr(x) (NNODES + x)

#define abs_idx(x, y) (x*NPROG + y)
#define cut_idx(x, y) (NPROG*NPROG + NPROG*x + y)
#define cut_cut_idx(x, y) (NPROG*NPROG*2 + NPROG*x + y)
#define cycle_idx(x) (NPROG*NPROG*3 + x)
#define cycle_dist_idx(x) (NPROG*NPROG*3 + NPROG + x)

#define min(x, y) (x < y ? x : y)

void abstract(unsigned int graph[NMATRIX],
              unsigned int abstraction[ABSSIZE]) {
  unsigned int paths[NNODES*NNODES];
  unsigned int cycles[NNODES];
  unsigned int cuts[NNODES*NNODES];
  unsigned int len, clen;
  int i, x, y, z, c, px, py;

  for (i = 0; i < NNODES*NNODES; i++) {
    paths[i] = INF;
    cuts[i] = INF;
  }

  for (i = 0; i < ABSSIZE; i++) {
    abstraction[i] = INF;
  }

  for (x = 0; x < NNODES; x++) {
    paths[idx(x, x)] = 0;

    if (graph[x] == x) {
      cycles[x] = 1;
    } else {
      cycles[x] = INF;
    }
  }

  for (i = 0; i < NNODES; i++) {
    for (x = 0; x < NNODES; x++) {
      y = graph[x];

      for (z = 0; z < NNODES; z++) {
        len = paths[idx(z, x)];

        if (len != INF) {
          len = len + 1;
          paths[idx(z, y)] = min(len, paths[idx(z, y)]);
        }
      }
    }
  }

  for (x = 0; x < NNODES; x++) {
    for (y = 0; y < NNODES; y++) {
      if (x != y &&
          paths[idx(x, y)] != INF &&
          paths[idx(y, x)] != INF) {
        len = paths[idx(x, y)] + paths[idx(y, x)];
        cycles[x] = min(cycles[x], len); 
      }

      for (z = 0; z < NNODES; z++) {
        if (paths[idx(x, z)] != INF &&
            paths[idx(y, z)] != INF) {
          c = cuts[idx(x, y)];
          len = paths[idx(x, z)];
          clen = paths[idx(x, c)];

          if (len < clen) {
            cuts[idx(x, y)] = z;
            abstraction[cut_idx(x, y)] = len;
          }
        }
      }
    }
  }

  for (x = 0; x < NPROG; x++) {
    abstraction[cycle_idx(x)] = INF;
    abstraction[cycle_dist_idx(x)] = INF;
    px = graph[ptr(x)];

    for (y = 0; y < NNODES; y++) {
      if (paths[idx(x, y)] != INF && cycles[y] != INF) {
        len = paths[idx(x, y)];

        abstraction[cycle_dist_idx(x)] = min(len,
            abstraction[cycle_dist_idx(x)]);
        abstraction[cycle_idx(x)] = cycles[y];
      }
    }
  }

  for (x = 0; x < NPROG; x++) {
    for (y = 0; y < NPROG; y++) {
      px = graph[ptr(x)];
      py = graph[ptr(y)];

      abstraction[idx(x, y)] = paths[idx(px, py)];

      unsigned int cxy = cuts[idx(px, py)];
      unsigned int cyx = cuts[idx(py, px)];

      if (cxy != INF && cyx != INF) {
        abstraction[cut_cut_idx(x, y)] = paths[idx(cxy, cyx)];
      } else {
        abstraction[cut_cut_idx(x, y)] = INF;
      }
    }
  }
}

int is_valid_heap(unsigned int graph[NMATRIX]) {
  unsigned int nullp = graph[ptr(0)];
  unsigned int x, px;

  if (graph[nullp] != INF) {
    return 0;
  }

  for (x = 0; x < NNODES; x++) {
    if (graph[x] == INF) {
      if (x != px) {
        return 0;
      }
    } else if (graph[x] >= NNODES) {
      return 0;
    }
  }

  for (x = 0; x < NPROG; x++) {
    px = graph[ptr(x)];

    if (px >= NPROG) {
      return 0;
    }
  }

  return 1;
}

int succ(unsigned int graph[NMATRIX], unsigned int x) {
  return graph[x];
}

int heaps_isomorphic(unsigned int graph1[NMATRIX],
                     unsigned int graph2[NMATRIX]) {
  unsigned int isomorphism[NNODES];
  int i, x, x2, y1, y2;
  int px, px2;


  for (i = 0; i < NNODES; i++) {
    isomorphism[i] = INF;
  }

  for (i = 0; i < NPROG; i++) {
    px = graph1[ptr(i)];
    px2 = graph2[ptr(i)];

    if (isomorphism[px] != INF) {
      if (isomorphism[px] != px2) {
        return 0;
      }
    } else {
      isomorphism[px] = px2;
    }
  }

  for (i = 0; i < NNODES; i++) {
    for (x = 0; x < NNODES; x++) {
      if (isomorphism[x] != INF) {
        y1 = succ(graph1, x);

        x2 = isomorphism[x];
        y2 = succ(graph2, x2);

        if (y1 == INF) {
          if (y2 != INF) {
            return 0;
          }
        } else if (isomorphism[y1] == INF) {
          isomorphism[y1] = y2;
        } else if (isomorphism[y1] != y2) {
          return 0;
        }
      }
    }
  }

  return 1;
}

int abstractions_equal(unsigned int abs1[ABSSIZE],
                       unsigned int abs2[ABSSIZE]) {
  int i;

  for (i = 0; i < ABSSIZE; i++) {
    if (abs1[i] != abs2[i]) {
      return 0;
    }
  }

  return 1;
}

int main(void) {
  unsigned int heap1[NMATRIX];
  unsigned int heap2[NMATRIX];
  unsigned int abs1[ABSSIZE], abs2[ABSSIZE];

  abstract(heap1, abs1);
  abstract(heap2, abs2);

  if (abstractions_equal(abs1, abs2) &&
      is_valid_heap(heap1) &&
      is_valid_heap(heap2)) {
    assert(heaps_isomorphic(heap1, heap2));
  }
}
