#include <stddef.h>
#include <limits.h>

/*@ predicate sorted(int* arr, integer end) =
      \forall integer i, j ; 0 <= i <= j < end ==> arr[i] <= arr[j] ;
    predicate element_level_sorted(int* array, integer end) =
      \forall integer i ; 0 <= i < end-1 ==> array[i] <= array[i+1] ; 
*/

/*@ requires \valid_read(arr + (0 .. len-1));
    requires sorted(arr, len) ;
*/
size_t bsearch(int* arr, size_t len, int value);

/*@ ghost
  /@
    requires \forall integer i ; 0 <= i < len-1 ==> arr[i] <= arr[i+1] ;
    assigns  \nothing ;
    ensures  \forall integer i, j ; 0 <= i <= j < len ==> arr[i] <= arr[j] ;
  @/
  void element_level_sorted_implies_sorted(int* arr, size_t len){
    /@
      loop invariant 0 <= i <= len ;
      loop invariant sorted(arr, i) ;
      loop assigns i ;
      loop variant len-i ;
    @/
    for(size_t i = 0 ; i < len ; ++i){
      /@ assert 0 < i ==> arr[i-1] <= arr[i] ; @/
    }
  }
*/

/*@ ghost
  /@
    requires \forall integer i ; 0 <= i < len-1 ==> arr[i] <= arr[i+1] ;
    assigns  \nothing ;
    ensures  0 <= i <= j < len ==> arr[i] <= arr[j] ;
  @/
  void element_level_sorted_implies_greater(int* arr, size_t len, size_t i, size_t j){
    element_level_sorted_implies_sorted(arr, len);
  }
*/

/*@ ghost
  /@
    requires \forall integer i ; 0 <= i < len-1 ==> arr[i] <= arr[i+1] ;
    requires 0 <= i <= j < len ;
    assigns  \nothing ;
    ensures  arr[i] <= arr[j] ;
  @/
  void element_level_sorted_implies_greater_2(int* arr, size_t len, size_t i, size_t j){
    element_level_sorted_implies_sorted(arr, len);
  }
*/
