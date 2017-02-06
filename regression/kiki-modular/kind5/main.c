#include <assert.h>

int main(int argc, char** argv)
{
  unsigned int limit;
  int a,b,sc, i = 0;
  __CPROVER_assume(a != b);

  while (i < limit) 
  {
    assert(a != b);
    sc = b; b = a; a = sc;
    i++;   
  } 

  return 0;
}

