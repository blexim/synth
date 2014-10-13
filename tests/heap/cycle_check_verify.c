//#include "heapabstract.h"
#include "heap_axioms.h"

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
  return (path(heap, p, q) && path(heap, l, p)) &&
         (
          (heap->stem[p] > 0 && heap->dist[p][q] > 0) ||
          (s_add(heap->dist[p][q], heap->dist[q][p]) == heap->cycle[l]) ||
          (alias(heap, p, q) && heap->cycle[l] != INF) ||
          (alias(heap, q, nil) && heap->cycle[l] == INF)
         );
}

int cond(abstract_heapt *heap) {
  return !alias(heap, p, q) &&
          !alias(heap, p, nil) &&
          !alias(heap, q, nil);
}

void body(abstract_heapt *pre, abstract_heapt *post) {
  abstract_heapt p1, p2, p3;
  abstract_heapt *s = pre;

  if (!alias(s, p, nil)) {
    abstract_lookup(p, p, s, &p1);

    if (!alias(&p1, q, nil)) {
      abstract_lookup(q, q, &p1, &p2);

      if (!alias(&p2, q, nil)) {
        abstract_lookup(q, q, &p2, post);
      } else {
        copy_abstract(&p2, post);
      }
    } else {
      copy_abstract(&p1, post);
    }
  } else if (!alias(pre, q, nil)) {
    abstract_lookup(q, q, pre, &p1);

    if (!alias(&p1, q, nil)) {
      abstract_lookup(q, q, &p1, post);
    } else {
      copy_abstract(&p1, post);
    }
  } else {
    copy_abstract(pre, post);
  }
}

int main(void) {
  abstract_heapt heap1;
  abstract_heapt heap2;
  abstract_heapt heap3;
  abstract_heapt tmp;

  /*
  __CPROVER_assume(all_axioms(&heap1));
  __CPROVER_assume(alias(&heap1, l, p));
  __CPROVER_assume(alias(&heap1, l, q));
  body(&heap1, &tmp);
  assert(inv(&tmp));
  */


  /*
  __CPROVER_assume(all_axioms(&heap2));
  __CPROVER_assume(inv(&heap2));
  __CPROVER_assume(cond(&heap2));
  body(&heap2, &tmp);
  assert(inv(&tmp));
  */

  __CPROVER_assume(all_axioms(&heap3));
  __CPROVER_assume(inv(&heap3));
  __CPROVER_assume(!cond(&heap3));
  if (alias(&heap3, q, nil)) {
    assert(heap3.cycle[l] == INF);
  } else {
    assert(heap3.cycle[l] != INF);
  }
}
