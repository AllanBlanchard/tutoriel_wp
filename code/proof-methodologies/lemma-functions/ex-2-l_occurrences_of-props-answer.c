#include <stddef.h>

/*@
  axiomatic Occurrences_Axiomatic{
    logic integer l_occurrences_of{L}(int value, int* in, integer from, integer to)
      reads in[from .. to-1];

    axiom occurrences_empty_range{L}:
      \forall int v, int* in, integer from, to;
        from >= to ==> l_occurrences_of{L}(v, in, from, to) == 0;

    axiom occurrences_positive_range_with_element{L}:
      \forall int v, int* in, integer from, to;
        (from < to && in[to-1] == v) ==>
      l_occurrences_of(v,in,from,to) == 1+l_occurrences_of(v,in,from,to-1);

    axiom occurrences_positive_range_without_element{L}:
      \forall int v, int* in, integer from, to;
        (from < to && in[to-1] != v) ==>
      l_occurrences_of(v,in,from,to) == l_occurrences_of(v,in,from,to-1);
  }
*/

/*@
  assigns  \nothing ;
  ensures  0 <= l_occurrences_of(v, arr, 0, len) <= len ;
*/
void occ_bounds(int v, int* arr, size_t len){
  /*@
    loop invariant 0 <= i <= len ;
    loop invariant 0 <= l_occurrences_of(v, arr, 0, i) <= i;
    loop assigns i ;
    loop variant len - i ;
  */
  for(size_t i = 0 ; i < len ; ++i);
}

/*@
  requires \forall integer i ; 0 <= i < len ==> arr[i] != v ;
  assigns \nothing ;
  ensures l_occurrences_of(v, arr, 0, len) == 0 ;
*/
void not_in_occ_0(int v, int* arr, size_t len){
  /*@
    loop invariant 0 <= i <= len ;
    loop invariant l_occurrences_of(v, arr, 0, i) == 0 ;
    loop assigns i ;
    loop variant len - i ;
  */
  for(size_t i = 0 ; i < len ; ++i);
}

/*@
  requires pos <= more ;
  assigns  \nothing ;
  ensures  l_occurrences_of(v, arr, 0, pos) <= l_occurrences_of(v, arr, 0, more) ;
*/
void occ_monotonic(int v, int* arr, size_t pos, size_t more){
  /*@
    loop invariant pos <= i <= more ;
    loop invariant l_occurrences_of(v, arr, 0, pos) <= l_occurrences_of(v, arr, 0, i) ;
    loop assigns i ;
    loop variant more - i ;
  */
  for(size_t i = pos ; i < more ; ++i);
}

/*@
  requires \valid_read(arr + (0.. len - 1)) ;
  requires l_occurrences_of(v, arr, 0, len) == 0 ;  
  assigns \nothing ;
  ensures \forall integer i ; 0 <= i < len ==> arr[i] != v ;
*/
void occ_0_not_in(int v, int* arr, size_t len){
  /*@
    loop invariant 0 <= i <= len ;
    loop invariant \forall integer j ; 0 <= j < i ==> arr[j] != v ;
    loop invariant l_occurrences_of(v, arr, 0, i) == 0 ;
    loop assigns i ;
    loop variant len - i ;
  */
  for(size_t i = 0 ; i < len ; ++i){
    if(arr[i] == v){
      //@ ghost occ_monotonic(v, arr, i+1, len) ;
      break ;
    }
  }
}

/*@
  requires \valid_read(arr + (0.. len - 1)) ;
  requires l_occurrences_of(v, arr, 0, len) > 0 ;
  assigns  \nothing ;
  ensures  0 <= \result < len ;
  ensures  arr[\result] == v ;
*/
size_t occ_pos_find(int v, int* arr, size_t len){
  /*@
    loop invariant 0 <= i <= len ;
    loop invariant \forall integer j ; 0 <= j < i ==> arr[j] != v ;
    loop invariant l_occurrences_of(v, arr, 0, i) == 0 ;
    loop assigns i ;
    loop variant len - i ;
  */
  for(size_t i = 0 ; i < len ; ++i){
    if(arr[i] == v){
      //@ ghost occ_monotonic(v, arr, i+1, len) ;
      return i ;
    }
  }
  return -1;
}

/*@
  requires \valid_read(arr + (0.. len - 1)) ;
  requires l_occurrences_of(v, arr, 0, len) > 0 ;
  assigns  \nothing ;
  ensures  \exists integer x ; 0 <= x < len && arr[x] == v ;
*/
void occ_pos_exists(int v, int* arr, size_t len){
  //@ ghost occ_pos_find(v, arr, len);
}
