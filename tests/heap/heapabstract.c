#include <stdio.h>
#include <assert.h>

#ifndef NNODES
 #define NNODES 5
#endif

#define NMATRIX NNODES*NNODES

#ifndef NPROG
 #define NPROG (NNODES/2)
#endif

#define ABSSIZE (NPROG*NPROG + NPROG*2)

#define INF 0xffffffff

#define idx(x, y) (x*NNODES + y)

#define abs_idx(x, y) (x*NPROG + y)
#define cycle_idx(x) (NPROG*NPROG + x)
#define cycle_dist_idx(x) (NPROG*NPROG + NPROG + x)

#define min(x, y) (x < y ? x : y)

void abstract(unsigned int graph[NMATRIX],
              unsigned int abstraction[ABSSIZE]) {
  unsigned int paths[NMATRIX];
  unsigned int cycles[NNODES];
  unsigned int len;
  int i, x, y, z;

  for (i = 0; i < ABSSIZE; i++) {
    paths[i] = INF;
  }

  for (x = 0; x < NNODES; x++) {
    paths[idx(x, x)] = 0;

    if (graph[idx(x, x)]) {
      cycles[x] = graph[idx(x, x)];
    } else {
      cycles[x] = INF;
    }
  }

  for (i = 0; i < NNODES; i++) {
    for (x = 0; x < NNODES; x++) {
      for (y = 0; y < NNODES; y++) {
        for (z = 0; z < NNODES; z++) {
          if (paths[idx(x, y)] != INF &&
              graph[idx(y, z)]) {
            len = paths[idx(x, y)] + graph[idx(y, z)];
            paths[idx(x, z)] = min(len, paths[idx(x, z)]);
          }
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
    }
  }

  for (x = 0; x < NPROG; x++) {
    abstraction[cycle_idx(x)] = INF;
    abstraction[cycle_dist_idx(x)] = INF;

    for (y = 0; y < NNODES; y++) {
      if (y < NPROG) {
        abstraction[abs_idx(x, y)] = paths[idx(x, y)];
      }

      if (paths[idx(x, y)] != INF && cycles[y] != INF) {
        len = paths[idx(x, y)];

        abstraction[cycle_dist_idx(x)] = min(len,
            abstraction[cycle_dist_idx(x)]);
        abstraction[cycle_idx(x)] = cycles[y];
      }
    }
  }
}

int is_valid_heap(unsigned int graph[NMATRIX]) {
  int x, y, cnt;

  for (x = 0; x < NNODES; x++) {
    cnt = 0;

    for (y = 0; y < NNODES; y++) {
      if (graph[idx(x, y)] != 0 &&
          graph[idx(x, y)] != 1) {
        return 0;
      }

      if (graph[idx(x, y)]) {
        cnt++;
      }
    }

    if (cnt > 1) {
      return 0;
    }
  }

  return 1;
}

void reachable(unsigned int graph[NMATRIX],
               unsigned int out[NNODES]) {
  int i, x, y;

  for (i = 0; i < NPROG; i++) {
    out[i] = 1;
  }

  for (i = NPROG; i < NNODES; i++) {
    out[i] = 0;
  }

  for (i = 0; i < NNODES; i++) {
    for (x = 0; x < NNODES; x++) {
      for (y = 0; y < NNODES; y++) {
        if (out[x] && graph[idx(x, y)]) {
          out[y] = 1;
        }
      }
    }
  }
}

int heaps_equal(unsigned int graph1[NMATRIX],
                unsigned int graph2[NMATRIX]) {
  unsigned int reaches1[NNODES], reaches2[NNODES];

  reachable(graph1, reaches1);
  reachable(graph2, reaches2);

  int x, y;

  for (x = 0; x < NNODES; x++) {
    if (reaches1[x] != reaches2[x]) {
      return 0;
    }

    for (y = 0; y < NNODES; y++) {
      if (reaches1[x] && reaches1[y]) {
        if (graph1[idx(x, y)] != graph2[idx(x, y)]) {
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
  unsigned int heap1[NMATRIX] = {0, 1, 0, 1};
  unsigned int heap2[NMATRIX] = {0, 1, 0, 0};
  unsigned int abs1[ABSSIZE], abs2[ABSSIZE];

  abstract(heap1, abs1);
  abstract(heap2, abs2);

  if (abstractions_equal(abs1, abs2) &&
      is_valid_heap(heap1) &&
      is_valid_heap(heap2)) {
    assert(heaps_equal(heap1, heap2));
  }
}
