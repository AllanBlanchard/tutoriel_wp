#include <stddef.h>


/*@
  requires \valid_read(arr + (0 .. len-1));
  requires Sorted:
    \forall integer i, j ; 0 <= i <= j < len ==> arr[i] <= arr[j] ;

  assigns \nothing ;

  behavior exists:
    assumes \exists integer j ; 0 <= j < len && arr[j] == value ;
    ensures 0 <= \result < len ;
    ensures arr[\result] == value ;

  behavior does_not_exists:
    assumes \forall integer j ; 0 <= j < len ==> arr[j] != value ;
    ensures \result == len ;

  complete behaviors ;
  disjoint behaviors ;
*/
size_t bsearch(int* arr, size_t len, int value){
  if(len == 0) return 0 ;
  
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
