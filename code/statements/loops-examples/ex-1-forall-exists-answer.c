#include <stddef.h>

/*@
  assigns \nothing ;
  ensures \result <==> (0 <= value <= 42) ;
*/
int pred(int value){
  return 0 <= value && value <= 42 ;
}

/*@
  requires \valid_read(array + (0 .. len-1)) ;
  assigns  \nothing ;
  ensures  \result <==> 
           (\forall integer i ; 0 <= i < len ==> 0 <= array[i] <= 42) ;
*/
int forall_pred(const int* array, size_t len){
  /*@
    loop invariant 0 <= i <= len ;
    loop invariant \forall integer j ; 0 <= j < i ==> 0 <= array[j] <= 42 ;
    loop assigns i ;
    loop variant len-i ;
  */
  for(size_t i = 0 ; i < len ; ++i){
    if(! pred(array[i])) return 0 ;
  }
  return 1 ;
}

/*@
  requires \valid_read(array + (0 .. len-1)) ;
  assigns  \nothing ;
  ensures  \result <==> 
           (\exists integer i ; 0 <= i < len && 0 <= array[i] <= 42) ;
*/
int exists_pred(const int* array, size_t len){
  /*@
    loop invariant 0 <= i <= len ;
    loop invariant \forall integer j ; 0 <= j < i ==> !(0 <= array[j] <= 42) ;
    loop assigns i ;
    loop variant len-i ;
  */
  for(size_t i = 0 ; i < len ; ++i){
    if(pred(array[i])) return 1 ;
  }
  return 0 ;
}


/*@
  requires \valid_read(array + (0 .. len-1)) ;
  assigns  \nothing ;
  ensures  \result <==> 
           (\forall integer i ; 0 <= i < len ==> !(0 <= array[i] <= 42)) ;
*/
int none_pred(const int* array, size_t len){
  return !exists_pred(array, len);
}

/*@
  requires \valid_read(array + (0 .. len-1)) ;
  assigns  \nothing ;
  ensures  \result <==> 
           (\exists integer i ; 0 <= i < len && !(0 <= array[i] <= 42)) ;
*/
int some_not_pred(const int* array, size_t len){
  return !forall_pred(array, len);
}
