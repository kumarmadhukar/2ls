#include <assert.h>


int foo(int a, int b, int c) 
{
  return a+1;
}

int bar(int a, int b, int c) 
{
  assert(a != b);
  return c;
}


// This main illustrates K-induction with proc call
// Safety can be shown for K = 4 after using summary TRUE for foo
// Only unwinding loop is required
int main(int argc, char** argv)
{
  unsigned int limit;
  int a,b,c,sc, i = 0;
  __CPROVER_assume(a != b && b != c && c != a);

  while (i < limit) {
//    assert(a != b);
    sc = c; c = b; b = a; a = sc;
    //a, b, c = c, a, b; parallel assignment;
    if (b == c) a = foo(a,b,c);
    //else //TODO: investigate why k-ind doesn't terminate if the call to bar is here
    c = bar(a,b,c);
    i++;
  } 

  return 0;
}

