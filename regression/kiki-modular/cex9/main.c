#include <assert.h>

int error(int k){
  assert(k != 2);
}

int inc(int x){
  return (x+1);
};

int inc_copy(int x){
  return (x+1);
};

int main(){
  int num = 0;
  num = inc_copy(num);
  num = inc(num);
  error(num);
  return 0;
}

	

