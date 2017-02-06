
#include <assert.h>

int bar(int k){
  return (k+1);
}

void foo(int x) {
  x = bar(x);
  assert(x>5);
}

int main() {
  int y;
  __CPROVER_assume(y<100000);
  if(y > 10) foo(y);
  return 0;
}


