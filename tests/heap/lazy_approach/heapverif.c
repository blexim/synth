#include "heaptheory.h"
#include "synth.h"

#define x 0
#define y 1
#define z 2

int main(void) {
  word_t pre[NARGS];
  word_t post[NARGS];

  if (well_formed(pre)) {
    update(pre, post, x, y);
    //assert(well_formed(post));

    assign(pre, post, x, y);
    //assert(well_formed(post));

    lookup(pre, post, x, y);
    assert(well_formed(post));

    alloc(pre, post, x);
    //assert(well_formed(post));
  }
}
