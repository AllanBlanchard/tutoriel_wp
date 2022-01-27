/* run.config
   OPT:
*/

#include <stddef.h>

/*@
  predicate
  swap_in_array{L1,L2}(int* a, integer b, integer e, integer i, integer j) =
    \true ; // to complete
*/

/*@
  axiomatic Permutation {
    // to complete
    predicate permutation{L, K}(int* a, integer b, integer e) ;
  }
*/

/*@
  predicate sorted(int* a, integer b, integer e) =
    \forall integer i, j; b <= i <= j < e ==> a[i] <= a[j];
*/

size_t min_idx_in(int* a, size_t beg, size_t end){
  return 0;
}

void swap(int* p, int* q){}

/*@
  requires beg < end && \valid(a + (beg .. end-1));
  assigns  a[beg .. end-1];
  ensures sorted(a, beg, end);
  ensures permutation{Pre, Post}(a,beg,end);
*/
void sort(int* a, size_t beg, size_t end){
  /*@
    loop invariant beg <= i <= end;
    loop invariant sorted(a, beg, i) && permutation{Pre, Here}(a, beg, end);
    loop invariant \forall integer j,k; beg <= j < i ==> i <= k < end ==> a[j] <= a[k];
    loop assigns i, a[beg .. end-1];
    loop variant end-i;
  */
  for(size_t i = beg ; i < end ; ++i){
    //@ ghost begin: ;
    size_t imin = min_idx_in(a, i, end);
    swap(&a[i], &a[imin]);
    //@ assert swap_in_array{begin,Here}(a,beg,end,i,imin);
  }
}
