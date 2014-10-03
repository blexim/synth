#include "heapabstract.h"

word_t nil = 0;
word_t l = 1;
word_t p = 2;
word_t q = 3;

int rank1(abstract_heapt *heap) {
  return heap->stem[p];
}

int rank2(abstract_heapt *heap) {
  return heap->dist[q][p];
}

int inv(abstract_heapt *heap) {
  return (heap->stem[p] > 0 && heap->dist[p][q] > 0) ||
          (s_add(heap->dist[p][q], heap->dist[q][p]) == heap->cycle[l]) ||
          (alias(heap, p, q) && heap->cycle[l] != INF) ||
          (alias(heap, q, nil) && heap->cycle[l] == INF);
}

int cond(abstract_heapt *heap) {
  return !alias(heap, p, q) &&
          !alias(heap, p, nil) &&
          !alias(heap, q, nil);
}

void body(abstract_heapt *pre, abstract_heapt *post) {
  abstract_heapt p1, p2;
  abstract_heapt *s = pre;

  if (!alias(s, p, nil)) {
    abstract_lookup(p, p, s, &p1);
    s = &p1;
  }

  if (!alias(s, q, nil)) {
    abstract_lookup(q, q, s, &p2);
    s = &p2;
  }

  if (!alias(s, q, nil)) {
    abstract_lookup(q, q, s, post);
  } else {
    copy_abstract(s, post);
  }
}

int main(void) {
  abstract_heapt heap1 = {
.dist={ { 0, 0, 0, 0 }, { 0, 0, 0, 0 }, { 0, 0, 0, 0 }, { 0, 0, 0, 0 } }, .cut={ { 0, 0, 0, 0 }, { 0, 0, 0, 0 }, { 0, 0, 0, 0 }, { 0, 0, 0, 0 } },
    .cut_cut={ { 0, 0, 0, 0 }, { 0, 0, 0, 0 }, { 0, 0, 0, 0 }, { 0, 0, 0, 0 } },
    .stem={ INF, INF, INF, INF },
    .cycle={ INF, INF, INF, INF }
  };
  abstract_heapt heap2;
  abstract_heapt heap3;
  abstract_heapt tmp;

  if (is_valid_abstract_heap(&heap1) &&
      alias(&heap1, l, p) &&
      alias(&heap1, l, q)) {
    body(&heap1, &tmp);
    assert(inv(&tmp));
  }

  /*
  if (is_valid_abstract_heap(&heap2) && inv(&heap2) && cond(&heap2)) {
    body(&heap2, &tmp);
    assert(inv(&tmp));
  }

  if (is_valid_abstract_heap(&heap3) && inv(&heap3) && !cond(&heap3)) {
    if (alias(&heap3, p, q)) {
      //assert(heap3.cycle[l] != INF);
    } else {
      //assert(heap3.cycle[l] == INF);
    }
  }
  */
}
