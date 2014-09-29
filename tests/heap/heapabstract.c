#include <stdio.h>
#include <assert.h>

#include "heapabstract.h"

void abstract(word_t graph[NMATRIX],
              word_t abstraction[ABSSIZE]) {
  word_t paths[NNODES*NNODES];
  word_t cuts[NNODES*NNODES];
  word_t cycles[NNODES];
  word_t len, clen;
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

        if (len != INF && y != INF) {
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
    }
  }

  for (x = 0; x < NPROG; x++) {
    for (y = 0; y < NPROG; y++) {
      for (z = 0; z < NNODES; z++) {
        if (paths[idx(x, z)] != INF &&
            paths[idx(y, z)] != INF) {
          c = cuts[idx(x, y)];
          len = paths[idx(x, z)];

          if (c != INF) {
            clen = paths[idx(x, c)];

            if (len < clen) {
              cuts[idx(x, y)] = z;
              abstraction[cut_idx(x, y)] = len;
            }
          } else {
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
      if (paths[idx(px, y)] != INF && cycles[y] != INF) {
        len = paths[idx(px, y)];

        abstraction[cycle_dist_idx(x)] = min(len, abstraction[cycle_dist_idx(x)]);
        abstraction[cycle_idx(x)] = cycles[y];
      }
    }
  }

  for (x = 0; x < NPROG; x++) {
    for (y = 0; y < NPROG; y++) {
      px = graph[ptr(x)];
      py = graph[ptr(y)];

      abstraction[idx(x, y)] = paths[idx(px, py)];

      word_t cxy = cuts[idx(px, py)];
      word_t cyx = cuts[idx(py, px)];

      if (cxy != INF && cyx != INF) {
        abstraction[cut_cut_idx(x, y)] = paths[idx(cxy, cyx)];
      } else {
        abstraction[cut_cut_idx(x, y)] = INF;
      }
    }
  }
}

int is_valid_heap(word_t graph[NMATRIX]) {
  word_t nullp = graph[ptr(0)];
  word_t x, px;

  if (nullp != 0) {
    return 0;
  }

  if (graph[nullp] != INF) {
    return 0;
  }

  for (x = 0; x < NNODES; x++) {
    if (graph[x] == INF) {
      if (x != nullp) {
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

int succ(word_t graph[NMATRIX], word_t x) {
  return graph[x];
}

int heaps_isomorphic(word_t graph1[NMATRIX],
                     word_t graph2[NMATRIX]) {
  word_t isomorphism[NNODES];
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

int abstractions_equal(word_t abs1[ABSSIZE],
                       word_t abs2[ABSSIZE]) {
  int i;

  for (i = 0; i < ABSSIZE; i++) {
    if (abs1[i] != abs2[i]) {
      return 0;
    }
  }

  return 1;
}
