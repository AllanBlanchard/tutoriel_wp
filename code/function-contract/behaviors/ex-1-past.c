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

/*@
  requires \valid(a) && \valid_read(b) ;
  requires \separated(a, b) ;

  assigns *a ;

  ensures \old(*b) ==> *a == 0 ;
  ensures ! \old(*b) ==> *a == \old(*a) ;
  ensures *b == \old(*b);
*/
void reset_1st_if_2nd_is_true(int* a, int const* b){
  if(*b) *a = 0 ;
}

/*@
  requires 1 <= m <= 12 ;
  ensures m \in { 2 } ==> \result == 28 ;
  ensures m \in { 1, 3, 5, 7, 8, 10, 12 } ==> \result == 31 ;
  ensures m \in { 4, 6, 9, 11 } ==> \result == 30 ;
*/
int day_of(int m){
  int days[] = { 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31 } ;
  return days[m-1] ;
}

/*@
  requires \valid(a) && \valid(b);
  assigns  *a, *b ;
  ensures  \old(*a) < \old(*b)  ==> *a == \old(*b) && *b == \old(*a) ;
  ensures  \old(*a) >= \old(*b) ==> *a == \old(*a) && *b == \old(*b) ;
*/
void max_ptr(int* a, int* b){
  if(*a < *b){
    int tmp = *b ;
    *b = *a ;
    *a = tmp ;
  }
}
