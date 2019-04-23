#include <stddef.h>

/*@
  requires \valid_read(a + (beg .. end-1));
  requires beg < end;

  assigns  \nothing;

  ensures  \forall integer i; beg <= i < end ==> a[\result] <= a[i];
  ensures  beg <= \result < end;
*/
size_t min_idx_in(int* a, size_t beg, size_t end){
  size_t min_i = beg;

  /*@
    loop invariant beg <= min_i < i <= end;
    loop invariant \forall integer j; beg <= j < i ==> a[min_i] <= a[j];
    loop assigns min_i, i;
    loop variant end-i;
  */
  for(size_t i = beg+1; i < end; ++i){
    if(a[i] < a[min_i]) min_i = i;
  }
  return min_i;
}

/*@
  requires \valid(p) && \valid(q);
  assigns  *p, *q;
  ensures  *p == \old(*q) && *q == \old(*p);
*/
void swap(int* p, int* q){
  int tmp = *p; *p = *q; *q = tmp;
}


/*@
  predicate swap_in_array{L1,L2}(int* a, integer b, integer e, integer i, integer j) =
    b <= i < e && b <= j < e &&
    \at(a[i], L1) == \at(a[j], L2) &&
    \at(a[j], L1) == \at(a[i], L2) &&
    \forall integer k; b <= k < e && k != j && k != i ==>
      \at(a[k], L1) == \at(a[k], L2);

  axiomatic Permutation {
    predicate permutation{L1,L2}(int* a, integer b, integer e)
        reads \at(a[b .. e-1], L1);

    axiom reflexive{L1}: 
      \forall int* a, integer b,e ; permutation{L1,L1}(a, b, e);
    axiom swap{L1,L2}:
      \forall int* a, integer b,e,i,j ;
        swap_in_array{L1,L2}(a,b,e,i,j) ==> permutation{L1,L2}(a, b, e);
    axiom transitive{L1,L2,L3}:
      \forall int* a, integer b,e ; 
        permutation{L1,L2}(a, b, e) && permutation{L2,L3}(a, b, e) ==> 
          permutation{L1,L3}(a, b, e);
  }
*/


/*@
  predicate sorted(int* a, integer b, integer e) =
    \forall integer i, j; b <= i <= j < e ==> a[i] <= a[j];
*/

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
