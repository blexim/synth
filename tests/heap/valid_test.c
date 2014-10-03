#include "heapabstract.h"

int main(void) {
  abstract_heapt heap = {
.dist={ { 0, INF, INF, INF }, { INF, 0, 0, 0 }, { INF, 0, 0, INF }, { INF, 0, INF, 0 } }, .cut={ { 0, INF, INF, INF }, { INF, 0, 0, 0 }, { INF, 0, 0, 1 }, { INF, 0, 4, 0 } },
    .cut_cut={ { 0, INF, 0, 0 }, { INF, 0, 0, 0 }, { 0, 0, 0, 0 }, { 0, 0, 6, 0 } },
    .stem={ INF, 2, 0, 0 },
    .cycle={ INF, 0, 0, 0 }
  };

  assert(is_valid_abstract_heap(&heap));
}
