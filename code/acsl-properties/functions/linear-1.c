#include <limits.h>

/*@
  logic integer ax_b(integer a, integer x, integer b) =
    a * x + b;
*/

/*@
  requires INT_MIN <= ax_b(3, x, 4) <= INT_MAX;
  assigns \nothing ;
  ensures \result == ax_b(3, x, 4);
*/
int function(int x){
  return 3*x + 4;
}

/*@
  requires INT_MIN <= 3*x ;
  requires INT_MIN <= ax_b(3, x, 4) <= INT_MAX;
  assigns \nothing ;
  ensures \result == ax_b(3, x, 4);
*/
int restricted(int x){
  return 3*x + 4;
}

/*@
  requires INT_MIN <= ax_b(3, x, 4) <= INT_MAX;
  assigns \nothing;
  ensures \result == ax_b(3, x, 4);
*/
int function_modified(int x){
  if(x > 0)
    return 3 * x + 4;
  else
    return 3 * (x + 2) - 2;
}

void mathematical_example(void){
  //@ assert ax_b(42, INT_MAX, 1) < ax_b(70, INT_MAX, 1) ;
}
