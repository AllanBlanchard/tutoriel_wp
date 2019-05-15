#include <limits.h>

/*@
  requires \valid(q) && \valid(r) && \separated(q, r);
  requires y != 0 && x > INT_MIN ;

  assigns *q, *r ;
  
  ensures *q * y + *r == x ;
*/
void div_rem(int x, int y, int* q, int* r){
  *q = x / y ;
  *r = x % y ;
}
