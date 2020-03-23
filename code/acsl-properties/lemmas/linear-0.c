#include <limits.h> 

/*@
  logic integer ax_b(integer a, integer x, integer b) =
    a * x + b;
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
  requires INT_MIN <= a*x <= INT_MAX ;
  requires INT_MIN <= ax_b(a,x,4) <= INT_MAX ;
  assigns \nothing ;
  ensures \result == ax_b(a,x,4); 
*/
int function(int a, int x){
  return a*x + 4;
}

/*@ 
  requires INT_MIN <= a*x <= INT_MAX ;
  requires INT_MIN <= a*y <= INT_MAX ;
  requires a > 0;
  requires INT_MIN <= ax_b(a,x,4) <= INT_MAX ;
  requires INT_MIN <= ax_b(a,y,4) <= INT_MAX ;
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
