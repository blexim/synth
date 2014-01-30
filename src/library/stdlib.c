#include "synth.h"
#include "library.h"

word_t plus(word_t a, word_t b) {
  return a + b;
}

word_t sub(word_t a, word_t b) {
  return a - b;
}

word_t mul(word_t a, word_t b) {
  return a * b;
}

word_t div(word_t a, word_t b) {
  __CPROVER_assume(b != 0);
  return a / b;
}

word_t one(word_t a, word_t b) {
  return 1;
}

word_t zero(word_t a, word_t b) {
  return 0;
}

word_t and(word_t a, word_t b) {
  return a & b;
}

word_t or(word_t a, word_t b) {
  return a | b;
}

word_t xor(word_t a, word_t b) {
  return a ^ b;
}

word_t not(word_t a, word_t b) {
  return ~a;
}

word_t eq(word_t a, word_t b) {
  return a == b;
}

word_t ne(word_t a, word_t b) {
  return a != b;
}

word_t lt(word_t a, word_t b) {
  return a < b;
}

word_t le(word_t a, word_t b) {
  return a <= b;
}

word_t shl(word_t a, word_t b) {
  return a << b;
}

word_t shr(word_t a, word_t b) {
  return a >> b;
}

typedef word_t (*comp_t)(word_t a, word_t b);

comp_t components[] = { plus, sub, mul, div, one, zero, and, or, xor, not,
  eq, ne, lt, le, shl, shr };

void assume_library(word_t lib[LIBSZ*3]) {
  int i;

  for (i = 0; i < LIBSZ; i++) {
    word_t o = lib[i*3];
    word_t a = lib[(i*3) + 1];
    word_t b = lib[(i*3) + 2];
    word_t r = components[i](a, b);

    __CPROVER_assume(o == r);
  }
}
