#include <assert.h>

int error(int k){
  assert(k != 3);
}

int inc(int x){
  return (x+1);
};

int main(){
  int num = 0;
  num = inc(num);
  num = inc(num);
  num = inc(num);
  error(num);
  return 0;
}

	

