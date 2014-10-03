#include "heapabstract.h"

int init_heap(abstract_heapt *heap) {
  word_t a, b;

  for (a = 0; a < NPROG; a++) {
    heap->stem[a] = INF;
    heap->cycle[a] = INF;

    for (b = 0; b < NPROG; b++) {
      heap->dist[a][b] = INF;
      heap->cut[a][b] = INF;
      heap->cut_cut[a][b] = INF;
    }

    heap->dist[a][a] = 0;
    heap->cut[a][a] = 0;
    heap->cut_cut[a][a] = 0;
  }
}

word_t x = 1;
word_t y = 2;

int main(void) {
  abstract_heapt init, pre, post;

  /*
  init_heap(&init);
  assert(is_valid_abstract_heap(&init));
  */

  __CPROVER_assume(is_valid_abstract_heap(&pre));

  abstract_lookup(x, y, &pre, &post);
  assert(is_valid_abstract_heap(&post));

  /*
  abstract_update(x, y, &pre, &post);
  assert(is_valid_abstract_heap(&post));
  */

  /*
  abstract_assign(x, y, &pre, &post);
  assert(is_valid_abstract_heap(&post));
  */

  /*
  abstract_inew(x, &pre, &post);
  assert(is_valid_abstract_heap(&post));
  */
}
