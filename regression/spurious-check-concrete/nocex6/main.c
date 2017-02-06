
#include <assert.h>

int main(int argc, char** argv)
{
  int y = 1;

  while(y<30){
    y++;
    assert(y<5);
  }

  return 0;
}

