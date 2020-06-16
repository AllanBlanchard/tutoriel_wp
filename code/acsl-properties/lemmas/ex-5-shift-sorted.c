/*@
  predicate shifted_cell{L1, L2}(int* p, integer shift) =
    \at(p[0], L1) == \at(p[shift], L2) ;
*/

size_t bsearch(int* arr, size_t beg, size_t end, int value);

/*@
  // lemma shifted_still_sorted{...}:
  // ...
  // lemma in_array_shifted{...}:
  // ...
*/

/*@
  requires sorted(array, 0, len) ;
  requires \valid(array + (0 .. len));
  requires in_array(value, array, 0, len) ;

  assigns array[1 .. len] ;
  
  ensures 1 <= \result <= len ;
*/
unsigned shift_and_search(int* array, size_t len, int value){
  shift_array(array, len, 1);
  return bsearch(array, 1, len+1, value);
}
