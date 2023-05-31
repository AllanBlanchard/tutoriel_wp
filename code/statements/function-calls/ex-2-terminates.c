#include <limits.h>
#include <stddef.h>

/*@ requires x > INT_MIN ;
    terminates \true ;
    assigns \nothing ;
    ensures x >= 0 ==> \result == x ;
    ensures x <  0 ==> \result == -x ;
*/
int abs(int x){
  return x >= 0 ? x : -x ;
}

/*@ requires INT_MIN < b - a <= INT_MAX ;
    terminates \true ;
    assigns \nothing ;
    ensures a < b  ==> a + \result == b ;
    ensures b <= a ==> a - \result == b ;
*/
int distance(int a, int b){
  return abs(b - a) ;
}

/*@ requires \valid_read(a + (0 .. len-1)) && \valid_read(b + (0 .. len-1));
    requires \valid(result + (0 .. len-1));
    requires \separated(a + (0..len-1), b + (0..len-1), result + (0..len-1));
    requires \forall integer i ; 0 <= i < len ==> 0 <= b[i] - a[i] <= INT_MAX ;

    terminates \true ;

    assigns result[0 .. len-1] ;

    ensures \forall integer i ; 0 <= i < len ==> a[i] + result[i] == b[i] ;
*/
void distances(int const* a, int const* b, int* result, size_t len){
  /*@ loop invariant 0 <= i <= len ;
      loop invariant \forall integer k ; 0 <= k < i ==> a[k] + result[k] == b[k] ;
      loop assigns i, result[0 .. len-1];
  */
  for(size_t i = 0 ; i < len ; ++i){
    result[i] = distance(a[i], b[i]);
  }
}

struct client ;

/*@ requires \valid(c) ;
    terminates \true ;
    assigns *c ;
*/
void initialize(struct client *c);

/*@ requires \valid(c) ;
    terminates \false ;
    assigns *c ;
    ensures \result \in { 0 , 1 } ;
*/
int connect(struct client *c);

/*@ requires \valid(c);
    terminates \true ;
    assigns *c ;
    ensures \result \in { 0 , 1 } ;
*/
int prepare(struct client *c){
  initialize(c);
  return connect(c);
}

/*@ terminates x > 0 ; */
void terminates_f1(int x){
  if(x <= 0) for(;;);
}

/*@ requires x > 0 ;
    terminates \true ;
*/
void terminates_f2(int x){
  if(x <= 0) for(;;);
}
