#include "synth.h"

void hint(solution_t prog) {
  /*
  __CPROVER_assume(prog.ops[0] == 10);
  __CPROVER_assume(prog.ops[1] == 7);
  __CPROVER_assume(prog.ops[2] == 10);
  __CPROVER_assume(prog.ops[3] == 7);
  __CPROVER_assume(prog.ops[4] == 5);
  __CPROVER_assume(prog.ops[5] == 2);
  __CPROVER_assume(prog.ops[6] == 10);
  __CPROVER_assume(prog.ops[7] == 5);
  */

  __CPROVER_assume(prog.parms[0] == 0);
  __CPROVER_assume(prog.parms[1] == 1);
  __CPROVER_assume(prog.parms[2] == 1);
  __CPROVER_assume(prog.parms[3] == 0);
  __CPROVER_assume(prog.parms[4] == 2);
  __CPROVER_assume(prog.parms[5] == 2);
  __CPROVER_assume(prog.parms[6] == 2);
  __CPROVER_assume(prog.parms[7] == 3);
  __CPROVER_assume(prog.parms[8] == 4);
  __CPROVER_assume(prog.parms[9] == 0x11111111);
  __CPROVER_assume(prog.parms[10] == 5);
  __CPROVER_assume(prog.parms[11] == 0x11111111);
  __CPROVER_assume(prog.parms[12] == 6);
  __CPROVER_assume(prog.parms[13] == 28);
  __CPROVER_assume(prog.parms[14] == 7);
  __CPROVER_assume(prog.parms[15] == 1);

  __CPROVER_assume(prog.xparms[0] == 0);
  __CPROVER_assume(prog.xparms[1] == 1);
  __CPROVER_assume(prog.xparms[2] == 0);
  __CPROVER_assume(prog.xparms[3] == 0);
  __CPROVER_assume(prog.xparms[4] == 0);
  __CPROVER_assume(prog.xparms[5] == 1);
  __CPROVER_assume(prog.xparms[6] == 0);
  __CPROVER_assume(prog.xparms[7] == 0);
  __CPROVER_assume(prog.xparms[8] == 0);
  __CPROVER_assume(prog.xparms[9] == 1);
  __CPROVER_assume(prog.xparms[10] == 0);
  __CPROVER_assume(prog.xparms[11] == 1);
  __CPROVER_assume(prog.xparms[12] == 0);
  __CPROVER_assume(prog.xparms[13] == 1);
  __CPROVER_assume(prog.xparms[14] == 0);
  __CPROVER_assume(prog.xparms[15] == 1);
}
