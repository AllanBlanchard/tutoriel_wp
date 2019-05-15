#include <limits.h>
#include <stddef.h>

/*@
  logic integer inc(integer x) = x+1 ;
*/

/*@
  requires \valid(array + (0 .. len));
  requires value + len <= INT_MAX ;
  assigns array[0 .. len-1];
  ensures len > 0 ==> array[0] == value ;
  ensures \forall integer j ; 1 <= j < len ==> array[j] == inc(array[j-1]) ;
*/
void iota(int* array, size_t len, int value){
  if(len){
    array[0] = value ;

    /*@
      loop invariant 1 <= i <= len ;
      loop invariant 
      \forall integer j ; 1 <= j < i ==> array[j] == inc(array[j-1]) ;
      loop invariant array[i-1] == value + (i-1) ;
      loop assigns i, array[1 .. len-1] ;
      loop variant len - i ;
    */
    for(size_t i = 1 ; i < len ; i++){
      array[i] = array[i-1]+1 ;
    }
  }
}
