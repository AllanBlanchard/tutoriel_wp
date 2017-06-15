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
  lemma ax_b_monotonic_neg:
    \forall integer a, b, i, j ;
      a <  0 ==> i <= j ==> ax_b(a, i, b) >= ax_b(a, j, b);
  lemma ax_b_monotonic_pos:
    \forall integer a, b, i, j ;
      a >  0 ==> i <= j ==> ax_b(a, i, b) <= ax_b(a, j, b);
  lemma ax_b_monotonic_nul:
    \forall integer a, b, i, j ;
      a == 0 ==> ax_b(a, i, b) == ax_b(a, j, b);
*/

/*@ 
  requires a > 0;
  requires limit_int_min_ax_b(a,4) < x < limit_int_max_ax_b(a,4);
  assigns \nothing ;
  ensures \result == ax_b(a,x,4); 
*/
int function(int a, int x){
  return a*x + 4;
}


/*@ 
  requires a > 0;
  requires limit_int_min_ax_b(a,4) < x < limit_int_max_ax_b(a,4) ;
  requires limit_int_min_ax_b(a,4) < y < limit_int_max_ax_b(a,4) ;
  assigns \nothing ;
*/
void foo(int a, int x, int y){
  int fmin, fmax;
  if(x < y){
    fmin = function(a,x);
    fmax = function(a,y);
  } else {
    fmin = function(a,y);
    fmax = function(a,x);
  }
  //@assert fmin <= fmax;
}
