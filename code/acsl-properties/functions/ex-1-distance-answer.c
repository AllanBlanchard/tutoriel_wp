#include <limits.h>

/*@
  logic integer abs(integer v) = (v < 0) ? -v : v ;
  logic integer distance(integer a, integer b) = abs(b-a) ;
*/

/*@
  requires distance(a, b) <= INT_MAX ;
  assigns \nothing ;
  ensures \result == distance(a, b) ;
*/
int distance(int a, int b){
  if(a < b) return b - a ;
  else return a - b ;
}
