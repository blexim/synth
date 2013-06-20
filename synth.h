#ifndef SYNTH_H

#ifndef SZ
 #define SZ 5
#endif

#ifndef WIDTH
 #define WIDTH 32
#endif

const int MAXOPCODE = 11;

// This has to be the smallest integer such that 2**(OPLEN) >= MAXOPCODE
#define OPLEN 4


typedef unsigned __CPROVER_bitvector[WIDTH] word_t;
typedef __CPROVER_bitvector[WIDTH] sword_t;

typedef unsigned __CPROVER_bitvector[OPLEN] op_t;
typedef unsigned __CPROVER_bitvector[1] bit_t;

typedef struct prog {
  op_t *ops;
  word_t *parms;
  bit_t *xparms;
} prog_t;

word_t exec(word_t, prog_t prog);
void test(word_t x, prog_t prog);

int check(word_t x, word_t z);
void tests(prog_t prog);

#endif // SYNTH_H
