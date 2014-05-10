int main() {
  int x = 1;

  while (nondet()) {
    x += 1;
  }

  assert(x % 2);
}
