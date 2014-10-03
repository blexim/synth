#include "heapabstract.h"
#include "heap_axioms.h"

int main(void) {
  concrete_heapt concrete;
  abstract_heapt abs;

  __CPROVER_assume(is_valid_heap(&concrete));

  abstract(&concrete, &abs);

  assert(alias_axioms(&abs));
  assert(path_axioms(&abs));
  assert(null_axioms(&abs));
  assert(cycle_axioms(&abs));
}
