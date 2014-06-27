#ifndef SYNTH_H

#ifndef SZ
 #define SZ 5
#endif

#ifdef SEARCH
 #define LEN(prog) (prog->len)
#else
 #define LEN(prog) SZ
#endif

#ifndef WIDTH
 #define WIDTH 32
#endif

#define WORDMASK ((1 << WIDTH) - 1)
#define PMASK ((1 << PWIDTH) - 1)
#define OPMASK ((1 << OPLEN) - 1)

#ifndef MWIDTH
 #define MWIDTH 23
#endif

#ifndef NARGS
 #define NARGS 1
#endif

#ifndef NEVARS
 #define NEVARS 0
#endif

#ifndef NPROGS
 #define NPROGS 1
#endif

#ifndef NRES
 #define NRES 1
#endif

#ifndef CONSTS
 #define CONSTS SZ
#endif

// The width of a pointer
#ifndef PWIDTH
 #define PWIDTH WIDTH
#endif

// Use this one to use the same instruction set as Brahma
//#define MAXOPCODE 17


#ifdef FLOAT
  // Use this one to enable floating point
  #define MAXOPCODE 26
#else
  #define MAXOPCODE 22
#endif

// This has to be the smallest integer such that 2**(OPLEN) >= MAXOPCODE
#define OPLEN 5

#ifndef SEARCH
  typedef unsigned __CPROVER_bitvector[WIDTH] word_t;
  typedef __CPROVER_bitvector[WIDTH] sword_t;
  //typedef __CPROVER_floatbv[WIDTH][MWIDTH] fword_t;
  typedef float fword_t;

  typedef unsigned __CPROVER_bitvector[PWIDTH] param_t;
  typedef unsigned __CPROVER_bitvector[OPLEN] op_t;
  typedef unsigned __CPROVER_bitvector[1] bit_t;
#else
  typedef unsigned int word_t;
  typedef int sword_t;
  typedef float fword_t;

  typedef unsigned int param_t;
  typedef unsigned int op_t;
  typedef unsigned int bit_t;
#endif

#if defined(SEARCH)
 #define assume(x) do {\
   if (!(x)) { execok = 0; \
    return; } \
 } while(0)
#elif defined(SYNTH)
 #define assume(x) __CPROVER_assume(x)
#else
 #define assume(x) assert(x)
#endif

typedef union fi {
  word_t x;
  fword_t f;
} fi_t;


typedef struct prog {
  unsigned int len;
  op_t ops[SZ];
  param_t params[SZ*3];
  word_t consts[CONSTS];
} prog_t;

typedef struct solution {
  prog_t progs[NPROGS];
  word_t evars[NEVARS];
} solution_t;

extern solution_t solution;
extern volatile int execok;

void exec(prog_t *prog, word_t args[NARGS], word_t res[NRES]);

void test(solution_t *solution, word_t args[NARGS]);
int check(solution_t *solution, word_t args[NARGS]);
void tests(solution_t *solution);

int exclude(prog_t *prog);
int wellformed(prog_t *prog);

#endif // SYNTH_H
