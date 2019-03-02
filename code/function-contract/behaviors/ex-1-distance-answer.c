#include <limits.h>

/*@
  requires a < b  ==> b - a <= INT_MAX ;
  requires b <= a ==> a - b <= INT_MAX ;

  assigns \nothing ;

  behavior inf:
    assumes a < b ;
    ensures a + \result == b ;

  behavior sup:
    assumes b <= a ;
    ensures a - \result == b ;

  complete behaviors ;
  disjoint behaviors ;
*/
int distance(int a, int b){
  if(a < b) return b - a ;
  else return a - b ;
}
