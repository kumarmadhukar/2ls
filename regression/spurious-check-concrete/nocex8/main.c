
#include <assert.h>

void fail(void) 
{ 
  assert(0);
}

int main(void) 
{ 
  int tmp = 0;
  if(tmp)
    fail();
  return 0;
}

