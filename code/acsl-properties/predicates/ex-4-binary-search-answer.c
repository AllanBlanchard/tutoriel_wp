#include <stddef.h>


/*@ 
  predicate sorted(int* arr, integer begin, integer end) =
    \forall integer i, j ; begin <= i <= j < end ==> arr[i] <= arr[j] ;

  predicate sorted(int* arr, integer end) =
    sorted(arr, 0, end);

  predicate in_array(int value, int* arr, integer begin, integer end) =
    \exists integer j ; begin <= j < end && arr[j] == value ;

  predicate in_array(int value, int* arr, integer end) =
    in_array(value, arr, 0, end) ;
*/

/*@
  requires \valid_read(arr + (0 .. len-1));
  requires sorted(arr, len) ;

  assigns \nothing ;

  behavior exists:
    assumes in_array(value, arr, len);
    ensures 0 <= \result < len ;
    ensures arr[\result] == value ;

  behavior does_not_exists:
    assumes !in_array(value, arr, len);
    ensures \result == len ;

  complete behaviors ;
  disjoint behaviors ;
*/
size_t bsearch(int* arr, size_t len, int value){
  if(len == 0) return len ;
  
  size_t low = 0 ;
  size_t up = len ;

  /*@
    loop invariant 0 <= low && up <= len ;
    loop invariant 
      \forall integer i ; 0 <= i < len && arr[i] == value ==> low <= i < up ;
    loop assigns low, up ;
    loop variant up - low ;
  */
  while(low < up){
    size_t mid = low + (up - low)/2 ;
    if     (arr[mid] > value) up = mid ;
    else if(arr[mid] < value) low = mid+1 ;
    else return mid ;
  }
  return len ;
}
