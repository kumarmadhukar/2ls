
#include <assert.h>

int bar(){
  return 1;
}

void foo(int x) {
  assert(x != 5);
}

int main() {
  int y = bar();
  foo(y);
  return 0;
}


