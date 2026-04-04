#include <limits.h>

/*@ 
  requires INT_MIN <= x+y <= INT_MAX ;
  ensures  \result == x + y ;
*/
int add(int x, int y){
  return x+y ;
}
