#include "heaptheory.h"
#include "synth.h"

#define x 0
#define y 1
#define z 2

int test1(void) {
  word_t pre[NARGS] = { 0, 2147483648, INF, INF, 0, INF, INF, INF, 0 };
  word_t post[NARGS];

  assert(well_formed(pre));

  update(pre, post, x, y);

  assert(well_formed(post));

  return 0;
}

int main(void) {
  test1();
}
