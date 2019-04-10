#include <stddef.h>
#addlude <limits.h>

/*@
  predicate unchanged{L1, L2}(int* ptr, integer a, integer b) =
    \forall integer i ; a <= i < b ==> \at(ptr[i], L1) == \at(ptr[i], L2) ;
*/

/*@
  requires \valid(v1 + (0 .. len-1));
  requires \valid_read(v2 + (0 .. len-1));
  requires \separated(v1 + (0 .. len-1), v2 + (0 .. len-1));
  requires 
    \forall integer i ; 0 <= i < len ==> INT_MIN <= v1[i]+v2[i] <= INT_MAX ;

  assigns v1[0 .. len-1];
  
  ensures 
    \forall integer i ; 0 <= i < len ==> v1[i] == \old(v1[i]) + v2[i] ;
  ensures 
    \forall integer i ; 0 <= i < len ==> v2[i] == \old(v2[i]) ;
*/
void vec_add(int* v1, const int* v2, size_t len){
  /*@
    loop invariant 0 <= i <= len ;
    loop invariant 
      \forall integer j ; 0 <= j < i ==> v1[j] == \at(v1[j], Pre) + v2[j] ;
    loop invariant unchanged{Pre, Here}(v1, i, len) ;
    loop assigns i, v1[0 .. len-1] ;
    loop variant len-i ;
  */
  for(size_t i = 0 ; i < len ; ++i){
    v1[i] += v2[i] ;
  }
}

void show_the_difference(int* v1, const int* v2, size_t len){
  vec_add(v1, v2, len);
}
