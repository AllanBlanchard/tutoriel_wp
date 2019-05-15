#include <limits.h>

/*@
  requires a < b  ==> b - a <= INT_MAX ;
  requires b <= a ==> a - b <= INT_MAX ;

  ensures a < b  ==> a + \result == b ;
  ensures b <= a ==> a - \result == b ;
*/
int distance(int a, int b){
  if(a < b) return b - a ;
  else return a - b ;
}
