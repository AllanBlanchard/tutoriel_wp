#include <limits.h>

/*@ requires x > INT_MIN ;
    assigns \nothing ;
    ensures x >  0 ==> \result == x ;
    ensures x <  0 ==> \result == -x ; */
int abs(int x){
  return x >= 0 ? x : -x ;
}

/*@ requires INT_MIN <= b - a <= INT_MAX;
    ensures a < b  ==> a + \result == b ;
    ensures b <= a ==> a - \result == b ;
*/
int distance(int a, int b){
  return abs(b - a) ;
}

/*@
  requires a < b  ==> b - a <= INT_MAX ;
  requires b <= a ==> a - b <= INT_MAX ;

  assigns \nothing ;

  ensures a < b  ==> a + \result == b ;
  ensures b <= a ==> a - \result == b ;
*/
int old_distance(int a, int b){
  if(a < b) return b - a ;
  else return a - b ;
}

extern int old ;
extern int new ;

/*@ requires INT_MIN <= b - a <= INT_MAX; */
void test(int a, int b){
  old = old_distance(a, b);
  new = distance(a, b);
  //@ assert old == new ;
}
