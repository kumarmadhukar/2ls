#include <assert.h>

//Simple K-Induction safe example for K=4
//No procedure calls; loop inv required: a != b != c

int main(int argc, char** argv)
{
  unsigned int limit;
  int a,b,c,sc, i = 0;
  __CPROVER_assume(a != b && b != c && c != a);

  while (i < limit) 
  {
    assert(a != b);
    sc = c; c = b; b = a; a = sc;
    //a, b, c = c, a, b; parallel assignment;
    i++;   
  } 

  return 0;
}

