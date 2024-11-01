/* run.config
   OPT:
*/

#include <limits.h>

/*@ inductive is_gcd(integer a, integer b, integer div) {
    case gcd_zero: \true ; // to complete
    case gcd_succ: \true ; // to complete
    }
*/

/*@
  requires a >= 0 && b >= 0 ;
  assigns \nothing ;
  // ensures ... ;
*/
int gcd(int a, int b){
  /*@
    loop invariant \forall integer t ; \true ; // to complete
  */
  while (b != 0){
    int t = b;
    b = a % b;
    a = t;
  }
  return a;
}
