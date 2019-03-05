#include <stddef.h>

/*@
  requires \valid_read(a_1 + (0 .. len-1)) ;
  requires \valid_read(a_2 + (0 .. len-1)) ;
  assigns  \nothing ;
  ensures \result <==>
          (\forall integer j ; 0 <= j < len ==> a_1[j] == a_2[j]) ;
*/
int equal(const int* a_1, const int* a_2, size_t len){
  /*@
    loop invariant 0 <= i <= len ;
    loop invariant \forall integer j ; 0 <= j < i ==> a_1[j] == a_2[j] ;
    loop assigns i ;
    loop variant len-i ;
  */
  for(size_t i = 0 ; i < len ; ++i){
    if(a_1[i] != a_2[i]) return 0 ;
  }
  return 1 ;
}

/*@
  requires \valid_read(a_1 + (0 .. len-1)) ;
  requires \valid_read(a_2 + (0 .. len-1)) ;
  assigns  \nothing ;
  ensures \result <==>
          (\exists integer j ; 0 <= j < len && a_1[j] != a_2[j]) ;
*/
int different(const int* a_1, const int* a_2, size_t len){
  return !equal(a_1, a_2, len);
}
