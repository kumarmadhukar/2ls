
// for complete to work faster: introduce a function call to modify an irrelevant variable

#include <assert.h>

unsigned nondet_int();

int foo(int a){

  a = a + (2*a) + (3*a);
  a = a - (2*a) - (3*a);
  a = -a;

  return a;
  
}

int main(){

  int x;
  int y;

  __CPROVER_assume(x > 0 and x < 10);
  
  while(x < 10000){
    x = x + 1;
    y = foo(y);

    if(nondet_int())
      break;
  }
  
  assert(x < 10001);
  
}
