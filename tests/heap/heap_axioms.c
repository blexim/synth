//#include "heapabstract.h"
#include "heap_axioms.h"

int is_valid_abstract_heap(abstract_heapt *heap) {
  word_t a, b, c;

  for (a = 0; a < NPROG; a++) {
    if (!alias(heap, 0, a) && !path(heap, a, 0)) {
      if (heap->cut[0][a] != INF) {
        return 0;
      }

      if (heap->cut[a][0] != INF) {
        return 0;
      }
    }

    if (!alias(heap, 0, a) && path(heap, 0, a)) {
      return 0;
    }

    if (path(heap, a, 0)) {
      if (heap->cycle[a] != INF) {
        return 0;
      }
    } else {
      if (heap->cycle[a] == INF) {
        return 0;
      }
    }

    if (!alias(heap, a, a)) {
      return 0;
    }

    if (heap->cut[a][a] != 0) {
      return 0;
    }

    if (heap->cut_cut[a][a] != 0) {
      return 0;
    }

    if (heap->cycle[a] == INF && heap->stem[a] != INF) {
      return 0;
    }

    if (heap->cycle[a] != INF && heap->stem[a] == INF) {
      return 0;
    }

    if (heap->cycle[a] == 0) {
      return 0;
    }

    for (b = 0; b < NPROG; b++) {
      if (alias(heap, a, b)) {
        if (!alias(heap, b, a)) {
          return 0;
        }

        if (heap->cut_cut[a][b] != 0 || heap->cut_cut[b][a] != 0) {
          return 0;
        }

        if (heap->cut[a][b] != 0 || heap->cut[a][b] != 0) {
          return 0;
        }

        if (heap->stem[a] != heap->stem[b]) {
          return 0;
        }

        if (heap->cycle[a] != heap->cycle[b]) {
          return 0;
        }
      }

      if (path(heap, a, b)) {
        if (s_add(heap->cut[a][b], heap->cut_cut[a][b]) != heap->dist[a][b]) {
          return 0;
        }

        if (heap->cut[b][a] != 0) {
          return 0;
        }

        if (heap->cycle[a] != heap->cycle[b]) {
          return 0;
        }

        if (heap->stem[b] > heap->stem[a]) {
          return 0;
        }

        if (s_sub(heap->stem[a], heap->dist[a][b]) != heap->stem[b]) {
          return 0;
        }

        if (heap->stem[a] != INF) {
          if (s_sub(heap->dist[a][b], heap->cut_cut[a][b]) != heap->stem[a]) {
            return 0;
          }
        }

        if (heap->stem[a] == 0) {
          if (s_add(heap->cut_cut[a][b], heap->cut_cut[b][a]) != heap->cycle[a] &&
              s_add(heap->cut_cut[a][b], heap->cut_cut[b][a]) != 0) {
            return 0;
          }

          if (s_add(heap->cut_cut[a][b], heap->cut_cut[b][a]) == 0) {
            if (!alias(heap, a, b)) {
              return 0;
            }
          }

          if (!path(heap, b, a)) {
            return 0;
          }
        }
      }

      if (heap->cut[a][b] != INF) {
        if (heap->cut_cut[a][b] == INF) {
          return 0;
        }

        if (heap->cut[b][a] == INF) {
          return 0;
        }

        if (heap->cycle[a] != heap->cycle[b]) {
          return 0;
        }

        if (heap->cut_cut[a][b] > heap->cycle[a]) {
          return 0;
        }
      }

      if (heap->cut[a][b] == 0) {
        if (!path(heap, b, a)) {
          return 0;
        }
      }

      if (heap->cut[a][b] == INF) {
        if (heap->cut_cut[a][b] != INF) {
          return 0;
        }
      }

      if (alias(heap, a, b) != alias(heap, b, a)) {
        return 0;
      }

      if (heap->cut_cut[a][b] == 0) {
        if (heap->cut_cut[b][a] != 0) {
          return 0;
        }
      }

      if (heap->cut_cut[a][b] != INF && heap->cut_cut[a][b] != 0) {
        if (heap->cut_cut[b][a] == INF || heap->cut_cut[b][a] == 0) {
          return 0;
        }

        if (heap->cycle[a] == INF || heap->cycle[b] == INF) {
          return 0;
        }

        if (heap->cut[a][b] == INF || heap->cut[b][a] == INF) {
          return 0;
        }

        if (s_add(heap->cut_cut[a][b], heap->cut_cut[b][a]) != heap->cycle[a]) {
          return 0;
        }
      }

      if (path(heap, a, b) && path(heap, b, a)) {
        if (!alias(heap, a, b) &&
            s_add(heap->dist[a][b], heap->dist[b][a]) != heap->cycle[a]) {
          return 0;
        }

        if (!alias(heap, a, b)) {
          if (heap->cycle[a] == INF || heap->cycle[b] == INF) {
            return 0;
          }

          if (heap->stem[a] != 0 || heap->stem[b] != 0) {
            return 0;
          }
        }
      }

      for (c = 0; c < NPROG; c++) {
        if (path(heap, a, b) && path(heap, b, c)) {
          if (heap->dist[a][c] != s_add(heap->dist[a][b], heap->dist[b][c])) {
            return 0;
          }
        }

        if (path(heap, a, b) && path(heap, a, c)) {
          if (heap->dist[a][b] != s_add(heap->dist[a][c], heap->dist[c][b]) &&
              heap->dist[a][c] != s_add(heap->dist[a][b], heap->dist[b][c])) {
            return 0;
          }
        }

        if (alias(heap, a, b)) {
          if (heap->cut[a][c] != heap->cut[b][c]) {
            return 0;
          }

          if (heap->cut[c][a] != heap->cut[c][b]) {
            return 0;
          }

          if (heap->cut_cut[a][c] != heap->cut_cut[b][c]) {
            return 0;
          }

          if (heap->cut_cut[c][a] != heap->cut_cut[c][b]) {
            return 0;
          }
        }

        if (cut(heap, a, b) && cut(heap, a, c)) {
          if (s_add(heap->cut[b][a], heap->cut[a][c]) != s_add(heap->cut[a][b], heap->cut[b][c]) &&
              s_add(heap->cut[a][a], heap->cut[a][b]) != s_add(heap->cut[a][c], heap->cut[c][b]) &&
              heap->cut[a][b] != heap->cut[a][c]) {
            return 0;
          }
        }
      }
    }
  }

  return 1;
}

int alias_axioms(abstract_heapt *heap) {
  word_t a, b, c;

  for (a = 0; a < NPROG; a++) {
    // Alias is reflexive.
    if (!alias(heap, a, a)) {
      return 0;
    }

    // Alias is symmetric.
    for (b = 0; b < NPROG; b++) {
      if (alias(heap, a, b) && !alias(heap, b, a)) {
        return 0;
      }

      // Alias is transitive.
      for (c = 0; c < NPROG; c++) {
        if (alias(heap, a, b) && alias(heap, b, c) && !alias(heap, a, c)) {
          return 0;
        }
      }
    }
  }

  return 1;
}

int path_axioms(abstract_heapt *heap) {
  word_t a, b, c;

  // If we have a path a -> b -> c, then the
  // shortest path from a to c is via b.
  for (a = 0; a < NPROG; a++) {
    for (b = 0; b < NPROG; b++) {
      for (c = 0; c < NPROG; c++) {
        if (heap->dist[a][b] <= heap->dist[a][c]) {
          if (s_add(heap->dist[a][b], heap->dist[b][c]) != heap->dist[a][c]) {
            return 0;
          }
        }
      }
    }
  }

  return 1;
}

int null_axioms(abstract_heapt *heap) {
  word_t a;

  for (a = 0; a < NPROG; a++) {
    // There is no path from null to any other node.
    if (!alias(heap, a, nil)) {
      if (path(heap, nil, a)) {
        return 0;
      }
    }
  }

  return 1;
}

int cycle_axioms(abstract_heapt *heap) {
  word_t a, b, len;

  for (a = 0; a < NPROG; a++) {
    // Nothing has a 0 cycle.
    if (heap->cycle[a] == 0) {
      return 0;
    }

    // No stem <=> no cycle.
    if (heap->stem[a] == INF) {
      if (heap->cycle[a] != INF) {
        return 0;
      }
    } else {
      if (heap->cycle[a] == INF) {
        return 0;
      }
    }

    // Cycle <=> null unreachable.
    if (heap->cycle[a] == INF) {
      if (!path(heap, a, nil)) {
        return 0;
      }
    } else {
      if (path(heap, a, nil)) {
        return 0;
      }
    }
  }

  for (a = 0; a < NPROG; a++) {
    for (b = 0; b < NPROG; b++) {
      // If a -> b then a and b share the same cycle.
      if (path(heap, a, b)) {
        if (heap->cycle[a] != heap->cycle[b]) {
          return ;
        }
      }

      // If a -> b and b -> a and a != b, then a and b
      // are on a cycle of length a -> b + b -> a.
      if (path(heap, a, b) && path(heap, b, a) && !alias(heap, a, b)) {
        if (heap->stem[a] != 0) {
          return 0;
        }

        len = s_add(heap->dist[a][b], heap->dist[b][a]);
        if (heap->cycle[a] != len) {
          return 0;
        }
      }

      // If a -> b and a's stem is 0, then a and b are on the same cycle.
      if (path(heap, a, b) && heap->stem[a] == 0) {
        if (heap->stem[b] != 0) {
          return 0;
        }

        if (heap->cycle[a] != heap->cycle[b]) {
          return 0;
        }
      }
    }
  }

  return 1;
}

int acyclic(abstract_heapt *heap) {
  word_t a, b;

  for (a = 0; a < NPROG; a++) {
    if (heap->cycle[a] != INF) {
      return 0;
    }
  }

  return 1;
}

int no_sharing(abstract_heapt *heap) {
  word_t a, b;

  for (a = 0; a < NPROG; a++) {
    for (b = 0; b < NPROG; b++) {
      if (heap->cut[a][b] == 0) {
        if (!path(heap, b, a)) {
          return 0;
        }
      } else if (heap->cut[a][b] != 0) {
        if (heap->dist[a][b] != heap->cut[a][b]) {
          return 0;
        }
      }
    }
  }

  return 1;
}
