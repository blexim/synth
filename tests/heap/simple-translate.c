#include "synth.h"
#include "heaptheory.h"

#define x 0
#define y 1
#define nil 2

int prefix(word_t pre[NARGS]) {
  return (path_length(pre, x, nil) == path_length(pre, y, nil)) &&
          path(pre, x, nil) &&
          path(pre, y, nil) &&
          path_length(pre, x, x) == 0 &&
          path_length(pre, y, y) == 0 &&
          path_length(pre, nil, nil) == 0;
}

int guard(word_t args[NARGS]) {
  return !alias(args, x, nil) && !alias(args, y, nil);
}

int body(word_t args[NARGS]) {
  word_t post[NARGS];

  lookup(args, post, x, x);
  lookup(post, args, y, y);

  return 1;
}

int assertion(word_t args[NARGS]) {
  return alias(args, x, nil) && alias(args, y, nil);
}
