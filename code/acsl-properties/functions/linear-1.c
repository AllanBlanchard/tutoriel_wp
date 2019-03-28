#include <limits.h>

/*@
  logic integer ax_b(integer a, integer x, integer b) =
    a * x + b;
*/

/*@
  logic integer limit_int_min_ax_b(integer a, integer b) =
    (a == 0) ? (b > 0) ? INT_MIN : INT_MIN-b :
    (a <  0) ? (INT_MAX-b)/a :
               (INT_MIN-b)/a ;

  logic integer limit_int_max_ax_b(integer a, integer b) =
    (a == 0) ? (b > 0) ? INT_MAX-b : INT_MAX :
    (a <  0) ? (INT_MIN-b)/a :
               (INT_MAX-b)/a ;
*/

/*@
  requires limit_int_min_ax_b(3,4) < x < limit_int_max_ax_b(3,4);
  assigns \nothing ;
  ensures \result == ax_b(3,x,4); 
*/
int function(int x){
  return 3*x + 4;
}
