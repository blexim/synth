#include "synth.h"
#include "heap.h"

extern int pre(abstract_heapt *heap);
extern int cond(abstract_heapt *heap);
extern int body(abstract_heapt *pre, abstract_heapt *post);
extern int assertion(abstract_heapt *heap);

int inv(solution_t *solution, heap_factst *facts) {
  word_t args[NARGS];
  word_t res[NRES];
  word_t i;

  serialize_facts(facts, args);

  exec(&solution->progs[0], args, res);

  return res[0];
}

int check(solution_t *solution, word_t args[NARGS]) {
  abstract_heapt h, t;
  heap_factst hf, tf;

  deserialize_heap(args, &h);

  if (!valid_abstract_heap(&h)) {
    return 1;
  }

  consequences(&h, &hf);

  // Base.
  if (pre(&h)) {
    if (!inv(solution, &hf)) {
      return 0;
    }
  }

  // Induction.
  if (inv(solution, &hf) && cond(&h)) {
    if (!body(&h, &t)) {
      return 0;
    }

    consequences(&t, &tf);
    
    if (!inv(solution, &tf)) {
      return 0;
    }
  }

  // Property.
  if (inv(solution, &hf) && !cond(&h)) {
    if (!assertion(&h)) {
      return 0;
    }
  }

  return 1;
}
