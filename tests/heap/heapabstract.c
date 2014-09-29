#include <stdio.h>
#include <assert.h>

#include "heapabstract.h"

void abstract(concrete_heapt *concrete,
              abstract_heapt *abstract) {
  word_t paths[NNODES][NNODES];
  word_t cuts[NNODES][NNODES];
  word_t cycles[NNODES];
  word_t len, old_len, clen;
  int i, x, y, z, c, px, py;

  for (x = 0; x < NNODES; x++) {
    for (y = 0; y < NNODES; y++) {
      paths[x][y] = INF;
      cuts[x][y] = INF;
    }
  }

  for (x = 0; x < NNODES; x++) {
    paths[x][x] = 0;

    if (concrete->succ[x] == x) {
      cycles[x] = 1;
    } else {
      cycles[x] = INF;
    }
  }

  // Compute all-pairs shortest paths on the concrete heap.
  for (i = 0; i < NNODES; i++) {
    for (x = 0; x < NNODES; x++) {
      y = concrete->succ[x];

      for (z = 0; z < NNODES; z++) {
        len = paths[z][x];

        if (len != INF && y != INF) {
          len = len + 1;
          old_len = paths[z][y];
          paths[z][y] = min(len, old_len);
        }
      }
    }
  }

  // Identify cycles in the concrete heap.
  for (x = 0; x < NNODES; x++) {
    for (y = 0; y < NNODES; y++) {
      if (x != y &&
          paths[x][y] != INF &&
          paths[y][x] != INF) {
        len = paths[x][y] + paths[y][x];
        cycles[x] = min(cycles[x], len); 
      }
    }
  }

  // Identify cutpoints in the concrete heap.
  for (x = 0; x < NPROG; x++) {
    for (y = 0; y < NPROG; y++) {
      cuts[x][y] = INF;

      for (z = 0; z < NNODES; z++) {
        if (paths[x][z] != INF &&
            paths[y][z] != INF) {
          c = cuts[x][y];

          if (c == INF) {
            cuts[x][y] = z;
          } else {
            len = paths[x][z];
            clen = paths[x][c];

            if (len < clen) {
              cuts[x][y] = z;
            }
          }
        }
      }
    }
  }


  // Compute distances, cuts and cut-cut distances between all
  // program variables.
  for (x = 0; x < NPROG; x++) {
    for (y = 0; y < NPROG; y++) {
      px = concrete->ptr[x];
      py = concrete->ptr[y];

      abstract->dist[x][y] = paths[px][py];

      word_t cxy = cuts[px][py];
      word_t cyx = cuts[py][px];

      abstract->cut[x][y] = cxy;

      if (cxy != INF && cyx != INF) {
        //abstract->cut_cut[x][y] = paths[cxy][cyx];
        abstract->cut_cut[x][y] = INF;
      } else {
        abstract->cut_cut[x][y] = INF;
      }
    }
  }

  // Find the nearest cycle & its length for each program variable.
  for (x = 0; x < NPROG; x++) {
    abstract->stem[x] = INF;
    abstract->cycle[x] = INF;

    px = concrete->ptr[x];

    for (y = 0; y < NNODES; y++) {
      if (paths[px][y] != INF && cycles[y] != INF) {
        len = paths[px][y];
        old_len = abstract->stem[x];

        abstract->stem[x] = min(len, old_len);
        abstract->cycle[x] = cycles[y];
      }
    }
  }
}

int is_valid_heap(concrete_heapt *heap) {
  word_t nullp = heap->ptr[0];
  word_t x, px;

  if (nullp != 0) {
    return 0;
  }

  if (heap->succ[nullp] != INF) {
    return 0;
  }

  for (x = 0; x < NNODES; x++) {
    if (heap->succ[x] == INF) {
      if (x != nullp) {
        return 0;
      }
    } else if (heap->succ[x] >= NNODES) {
      return 0;
    }
  }

  for (x = 0; x < NPROG; x++) {
    px = heap->ptr[x];

    if (px >= NPROG) {
      return 0;
    }
  }

  return 1;
}

int succ(concrete_heapt *heap, word_t x) {
  return heap->succ[x];
}

int heaps_isomorphic(concrete_heapt *heap1,
                     concrete_heapt *heap2) {
  word_t isomorphism[NNODES];
  int i, x, x2, y1, y2;
  int px1, px2;


  for (i = 0; i < NNODES; i++) {
    isomorphism[i] = INF;
  }

  for (i = 0; i < NPROG; i++) {
    px1 = heap1->ptr[i];
    px2 = heap2->ptr[i];

    if (isomorphism[px1] != INF) {
      if (isomorphism[px1] != px2) {
        return 0;
      }
    } else {
      isomorphism[px1] = px2;
    }
  }

  for (i = 0; i < NNODES; i++) {
    for (x = 0; x < NNODES; x++) {
      if (isomorphism[x] != INF) {
        y1 = succ(heap1, x);

        x2 = isomorphism[x];
        y2 = succ(heap1, x2);

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

int abstractions_equal(abstract_heapt *abs1,
                       abstract_heapt *abs2) {
  int i, j;

  for (i = 0; i < NPROG; i++) {
    if (abs1->stem[i] != abs2->stem[i]) {
      return 0;
    }

    if (abs1->cycle[i] != abs2->cycle[i]) {
      return 0;
    }

    for (j = 0; j < NPROG; j++) {
      if (abs1->dist[i][j] != abs2->dist[i][j]) {
        return 0;
      }

      if (abs1->cut[i][j] != abs2->cut[i][j]) {
        return 0;
      }

      if (abs1->cut_cut[i][j] != abs2->cut_cut[i][j]) {
        return 0;
      }
    }
  }

  return 1;
}

#define LINEWIDTH 4

void print_concrete(concrete_heapt *heap) {
  int i;
  word_t y;
  char *ptrnames[] = {"NULL", "x", "y", "z", "w"};

  printf("\nSuccessors:");

  for (i = 0; i < NNODES; i++) {
    if (i % LINEWIDTH == 0) {
      printf("\n");
    }

    y = heap->succ[i];

    printf("%d -> %d;   ", i, y);
  }

  printf("\nPointers:");

  for (i = 0; i < NPROG; i++) {
    if (i % LINEWIDTH == 0) {
      printf("\n");
    }

    y = heap->ptr[i];

    if (i < sizeof(ptrnames)) {
      printf("%s == %d;  ", ptrnames[i], y);
    } else {
      printf("p%d == %d;  ", i, y);
    }
  }

  printf("\n");
}
