#include "synth.h"

void hint(solution_t prog) {
  __CPROVER_assume(prog.ops[0] == 4);
  __CPROVER_assume(prog.ops[1] == 5);
  __CPROVER_assume(prog.ops[2] == 0);
  __CPROVER_assume(prog.ops[3] == 7);
  __CPROVER_assume(prog.ops[4] == 10);
  __CPROVER_assume(prog.ops[5] == 3);
  __CPROVER_assume(prog.ops[6] == 6);
}
