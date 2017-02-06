#include <assert.h>


int bar(int a, int b, int c) 
{
  return c;
}

//This main illustrates need for refinement of bar
//based on spurious CEX
int main(int argc, char** argv)
{
  unsigned int limit;
  int a,b,c,sc, i = 0;
  __CPROVER_assume(a != b && b != c && c != a);

  while (i < limit) {
    assert(a != b);
    sc = c; c = b; b = a; a = bar(a,b,sc);
    //a, b, c = bar(a,b,c), a, b; parallel assignment;
    i++;
  } 

  return 0;
}

