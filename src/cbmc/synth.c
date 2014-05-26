#include "synth.h"
void test(solution_t *solution, word_t args[NARGS]) {
  __CPROVER_assume(check(solution, args));
}

int main(void) {
  solution_t solution;

  __CPROVER_assume(wellformed(&solution.prog));
  __CPROVER_assume(!exclude(&solution.prog));

  tests(&solution);

  assert(0);
}
