#include "synth.h"
#include "library.h"

#define component(e) do { \
  __CPROVER_assume(lib[idx] == (word_t) (e)); \
  idx += 3; \
} while (0)

#define x (lib[idx+1])
#define y (lib[idx+2])

void assume_library(word_t lib[LIBSZ*3]) {
  int idx = 0;

  component(x + y);
  component(x - y);
  component(x * y);
  __CPROVER_assume(y != 0);
  component(x / y);
  component(1);
  component(0);
  component(x & y);
  component(x | y);
  component(x ^ y);
  component(~x);
  component(x == y);
  component(x != y);
  component(x < y);
  component(x <= y);
  component(x << y);
  component(x >> y);
}
