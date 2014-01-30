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

  component(x & y);   // 0
  component(x | y);   // 1
  component(~x);      // 2
  component(x + 1);   // 3
  component(x - 1);   // 4
  component(x ^ y);   // 5
  component(x >> y);  // 6
  component(x + y);   // 7
  component(x - y);   // 8
  component(x == y);  // 9
  component(x != y);  // 10
  component(x < y);   // 11
  component(x <= y);  // 12
}
