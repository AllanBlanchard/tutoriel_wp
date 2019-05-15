#include <limits.h>

/*@
  ensures \result >= a && \result >= b;
*/
int max(int a, int b){
  return INT_MAX;
}

void foo(){
  int a = 42;
  int b = 37;
  int c = max(a,b);

  //@assert c == 42;
}
