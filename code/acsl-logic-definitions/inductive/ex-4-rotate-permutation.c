/* run.config
   DONTRUN:
*/

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
    // ...
*/

/*@
  assigns arr[beg .. end-1] ;
  ensures rotate{Pre, Post}(arr, beg, end) ;
*/
void rotate(int* arr, size_t beg, size_t end){
  int last = arr[end-1] ;
  for(size_t i = end-1 ; i > beg ; --i){
    arr[i] = arr[i-1] ;
  }
  arr[beg] = last ;
}


/*@
  inductive permutation{L1, L2}(int* arr, integer fst, integer last){
  case reflexive{L1}: // ...
  case rotate_left{L1,L2}: // ...
  case rotate_right{L1,L2}: // ...
  case transitive{L1,L2,L3}: // ...
  }
*/

/*@
  assigns arr[beg .. end-1] ;
  ensures permutation{Pre,Post}(arr, beg, end);
*/
void two_rotates(int* arr, size_t beg, size_t end){
  rotate(arr, beg, beg+(end-beg)/2) ;
  //@ assert permutation{Pre, Here}(arr, beg, end) ;
  rotate(arr, beg+(end-beg)/2, end) ;
}
