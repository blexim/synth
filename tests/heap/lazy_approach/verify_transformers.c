#include "heapabstract.h"

const word_t x = 1;
const word_t y = 2;

void verify_assign() {
  concrete_heapt heap1, heap2;
  abstract_heapt abs1, abs2, abs3;

  abstract(&heap1, &abs1);
  abstract_assign(x, y, &abs1, &abs2);

  concrete_assign(x, y, &heap1, &heap2);
  abstract(&heap2, &abs3);

  if (is_valid_heap(&heap1)) {
    assert(abstractions_equal(&abs2, &abs3));
  }
}

void verify_new() {
  concrete_heapt heap1, heap2;
  abstract_heapt abs1, abs2, abs3;

  abstract(&heap1, &abs1);
  abstract_new(x, &abs1, &abs2);

  concrete_new(x, &heap1, &heap2);
  abstract(&heap2, &abs3);

  if (is_valid_heap(&heap1)) {
    assert(abstractions_equal(&abs2, &abs3));
  }
}


void verify_lookup() {
  concrete_heapt heap1, heap2;
  abstract_heapt abs1, abs2, abs3;

  abstract(&heap1, &abs1);
  abstract_lookup(x, y, &abs1, &abs2);

  concrete_lookup(x, y, &heap1, &heap2);
  abstract(&heap2, &abs3);

  if (is_valid_heap(&heap1)) {
    assert(abstractions_equal(&abs2, &abs3));
  }
}

void verify_update() {
  concrete_heapt heap1, heap2;
  abstract_heapt abs1, abs2, abs3;

  concrete_update(x, y, &heap1, &heap2);
  abstract(&heap2, &abs3);

  abstract(&heap1, &abs1);
  abstract_update(x, y, &abs1, &abs2);

  if (is_valid_heap(&heap1)) {
    assert(abstractions_equal(&abs2, &abs3));
  }
}

void verify_concrete_update() {
  concrete_heapt heap1, heap2;

  concrete_update(x, y, &heap1, &heap2);

  if (is_valid_heap(&heap1)) {
    assert(is_valid_heap(&heap2));
  }
}

void verify_concrete_lookup() {
  concrete_heapt heap1, heap2;

  concrete_lookup(x, y, &heap1, &heap2);

  if (is_valid_heap(&heap1)) {
    assert(is_valid_heap(&heap2));
  }
}

void verify_concrete_assign() {
  concrete_heapt heap1, heap2;

  concrete_assign(x, y, &heap1, &heap2);

  if (is_valid_heap(&heap1)) {
    assert(is_valid_heap(&heap2));
  }
}

void verify_concrete_new() {
  concrete_heapt heap1, heap2;

  concrete_new(x, y, &heap1, &heap2);

  if (is_valid_heap(&heap1)) {
    assert(is_valid_heap(&heap2));
  }
}


void main(void) {
  /* verify_assign(); */
  /* verify_lookup(); */
  /* verify_update(); */
  verify_new();

  //verify_concrete_update();
  //verify_concrete_lookup();
  //verify_concrete_assign();
  //verify_concrete_new();

}
