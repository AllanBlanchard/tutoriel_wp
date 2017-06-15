#include <stddef.h>
#include "sort_spec.h"

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
  requires \valid(a + (beg .. end-1));
  requires beg < end;

  assigns  a[beg .. end-1];
  
  ensures sorted(a, beg, end);
  ensures permutation{Pre, Post}(a,beg,end);
*/
void sort(int* a, size_t beg, size_t end){
  /*@
    loop invariant beg <= i <= end;
    loop invariant permutation{Pre, Here}(a,beg,end);
    loop invariant sorted(a, beg, i);
    loop invariant \forall integer j,k; beg <= j < i ==> 
                     i <= k < end ==> a[j] <= a[k];

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

//loop invariant permutation{Pre, Here}(a,beg,end);

/*@
  requires \valid(a + (beg .. end-1));
  requires beg < end;

  assigns  a[beg .. end-1];
  
  ensures sorted(a, beg, end);
*/
void fail_sort(int* a, size_t beg, size_t end){
  /*@
    loop invariant beg <= i <= end;
    loop invariant \forall integer j; beg <= j < i ==> a[j] == 0;
    loop assigns i, a[beg .. end-1];
    loop variant end-i;
  */
  for(size_t i = beg ; i < end ; ++i)
    a[i] = 0;
}
