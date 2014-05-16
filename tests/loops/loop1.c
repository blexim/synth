int main() {
  int x = 1;

  while (nondet()) {
    x += 2;
  }

  assert(x % 2);
}
