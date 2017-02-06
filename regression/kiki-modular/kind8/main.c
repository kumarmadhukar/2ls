
// for concrete to work faster: a false assertion such that all counterexamples are valid counterexamples

#include <assert.h>

unsigned nondet_int();

int bar(int x){
  if((x > 0) || (x <= 0))
    assert(0);

  return 0;
}

int inc_or_dec(int x){
  if(nondet_int())
    x = x + 1;
  else
    x = x - 1;

  return x;
}

int main(){

  int k;
  int counter = 0

  while(counter < 100000){
    k = inc_or_dec(k);
    if(nondet_int())
      break;
    counter++;
  }
  
  bar(k);
  
  return 0;
  
}
