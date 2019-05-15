/*@ 
  predicate sorted(int* array, integer begin, integer end) =
    \forall integer i, j ; begin <= i <= j < end ==> array[i] <= array[j] ;

  predicate unchanged{L1, L2}(int *array, integer begin, integer end) =
    \forall integer i ; begin <= i < end ==> 
      \at(array[i], L1) == \at(array[i], L2) ;
*/

/*@
  lemma unchanged_sorted{L1, L2}:
    \forall int* array, integer b, integer e ;
      sorted{L1}(array, b, e) ==>
      unchanged{L1, L2}(array, b, e) ==> 
        sorted{L2}(array, b, e) ;
*/
