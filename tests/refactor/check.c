#include "synth.h"
#include "refactor.h"

extern void body(word_t x);

word_t mapped;
word_t emitted;

void emit(word_t x) {
  mapped = x;
  emitted = 1;
}

int check(solution_t *solution, word_t args[NARGS]) {
  word_t res[NRES];
  word_t map_out, filter_out;

  emitted = 0;

  body(args[0]);

  exec(&solution->progs[0], args, res);
  map_out = res[0];

  exec(&solution->progs[1], args, res);
  filter_out = res[0];

  if (emitted) {
    if (!filter_out) {
      return 0;
    }

    if (map_out != mapped) {
      return 0;
    }
  } else {
    if (filter_out) {
      return 0;
    }
  }

  return 1;
}
