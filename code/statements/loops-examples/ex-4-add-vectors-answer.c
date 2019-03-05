#include <stddef.h>
#include <limits.h>

/*@
  requires \valid(v_res + (0 .. len-1));
  requires \valid_read(v1 + (0 .. len-1));
  requires \valid_read(v2 + (0 .. len-1));
  requires \separated(v1 + (0 .. len-1), v_res + (0 .. len-1));
  requires \separated(v2 + (0 .. len-1), v_res + (0 .. len-1));

  requires 
    \forall integer i ; 0 <= i < len ==> INT_MIN <= v1[i]+v2[i] <= INT_MAX ;

  assigns v_res[0 .. len-1];
  
  ensures \forall integer i ; 0 <= i < len ==> v_res[i] == v1[i] + v2[i] ;
  ensures \forall integer i ; 0 <= i < len ==> v1[i] == \old(v1[i]) ;
  ensures \forall integer i ; 0 <= i < len ==> v2[i] == \old(v2[i]) ;
*/
void add_vectors(int* v_res, const int* v1, const int* v2, size_t len){
  /*@
    loop invariant 0 <= i <= len ;
    loop invariant 
      \forall integer j ; 0 <= j < i ==> v_res[j] == v1[j] + v2[j] ;
    loop assigns i, v_res[0 .. len-1] ;
    loop variant len-i ;
  */
  for(size_t i = 0 ; i < len ; ++i){
    v_res[i] = v1[i] + v2[i] ;
  }
}
