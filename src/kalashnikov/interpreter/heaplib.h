#ifndef HEAPLIB_H
#define HEAPLIB_H

#include "synth.h"

typedef struct node {
  word_t v;
  word_t n;
} node_t;

int is_path(word_t x, word_t y, word_t vars[NARGS]);

int is_ptr(word_t p);
word_t deref(word_t p, word_t vars[NARGS]);

#endif
