#include "synth.h"

typedef struct prog1 {
  op_t ops[1];
  word_t parms[2];
  bit_t xparms[2];
} prog1_t;

prog1_t excludes1[] = {
  { {0}, {0, 0}, {0, 1} },
  { {1}, {0, 0}, {0, 1} },
  { {2}, {0, 1}, {0, 1} },
  { {3}, {0, 1}, {0, 1} },
  { {5}, {0, 0}, {0, 0} },
  { {5}, {0, 0xffffffff & ((1 << SZ) -1)}, {0, 1} },
  { {6}, {0, 0}, {0, 0} },
  { {6}, {0, 0}, {0, 1} },
  { {7}, {0, 0}, {0, 1} },
  { {9}, {0, 0}, {0, 1} },
  { {10}, {0, 0}, {0, 1} },
  { {11}, {0, 0}, {0, 1} }
};

int exclude_1(op_t op, word_t p1, word_t p2, bit_t x1, bit_t x2) {
  for (int i = 0; i < sizeof(excludes1); i++) {
    for (int j = 0; j < 1; j++) {
      if (excludes1[i].ops[j] == op &&
          excludes1[i].parms[j*2] == p1 &&
          excludes1[i].parms[j*2+1] == p2 &&
          excludes1[i].xparms[j*2] == x1 &&
          excludes1[i].xparms[j*2+1] == x2) {
        return 1;
      }
    }
  }

  return 0;
}

void exclude(prog_t prog) {
  for (unsigned int i = 0; i < SZ; i++) {
    __CPROVER_assume(!exclude_1(prog.ops[i],
          prog.parms[i*2], prog.parms[i*2+1],
          prog.xparms[i*2], prog.xparms[i*2+1]));
  }
}
