#include <stddef.h>

/*@
  predicate shifted{L1, L2}(int* arr, integer fst, integer last, integer shift) =
    \forall integer i ; fst <= i < last ==> \at(arr[i], L1) == \at(arr[i+shift], L2) ;
*/
/*@
  predicate unchanged{L1, L2}(int *a, integer begin, integer end) =
    shifted{L1, L2}(a, begin, end, 0) ;
*/

/*@
  predicate rotate{L1, L2}(int* arr, integer fst, integer last) =
    shifted{L1, L2}(arr, fst, last-1, 1) &&
    shifted{L1, L2}(arr, last-1, last, fst-last+1) ;
*/

/*@
  requires beg < end && \valid(arr + (beg .. end-1)) ;
  assigns arr[beg .. end-1] ;
  ensures rotate{Pre, Post}(arr, beg, end) ;
*/
void rotate(int* arr, size_t beg, size_t end){
  int last = arr[end-1] ;
  /*@
    loop invariant beg <= i <= end-1 ;
    loop invariant unchanged{Pre, Here}(arr, beg, i+1) ;
    loop invariant shifted{Pre, Here}(arr, i, end-1, 1) ;
    loop assigns arr[beg+1 .. end-1], i ;
    loop variant i ;
  */
  for(size_t i = end-1 ; i > beg ; --i){
    arr[i] = arr[i-1] ;
  }
  arr[beg] = last ;
}


/*@
  inductive permutation{L1, L2}(int* arr, integer fst, integer last){
  case reflexive{L1}: 
    \forall int* a, integer b,e ; permutation{L1,L1}(a, b, e);
  case rotate_left{L1,L2}:
    \forall int* a, integer b, e, i ;
      b < i <= e ==> rotate{L1, L2}(a, b, i) ==> unchanged{L1, L2}(a, i, e) ==>
        permutation{L1, L2}(a, b, e) ;
  case rotate_right{L1,L2}:
    \forall int* a, integer b, e, i ;
      b <= i < e ==> unchanged{L1, L2}(a, b, i) ==> rotate{L1, L2}(a, i, e) ==>
        permutation{L1, L2}(a, b, e) ;
  case transitive{L1,L2,L3}:
    \forall int* a, integer b,e ; 
      permutation{L1,L2}(a, b, e) && permutation{L2,L3}(a, b, e) ==> 
        permutation{L1,L3}(a, b, e);
  }
*/

/*@
  requires beg+1 < end && \valid(arr + (beg .. end-1)) ;
  assigns arr[beg .. end-1] ;
  ensures permutation{Pre,Post}(arr, beg, end);
*/
void two_rotates(int* arr, size_t beg, size_t end){
  rotate(arr, beg, beg+(end-beg)/2) ;
  //@ assert permutation{Pre, Here}(arr, beg, end) ;
  rotate(arr, beg+(end-beg)/2, end) ;
}
