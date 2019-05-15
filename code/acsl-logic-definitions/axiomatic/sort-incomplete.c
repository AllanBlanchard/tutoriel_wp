#include <stddef.h>

size_t min_idx_in(int* a, size_t beg, size_t end);
void swap(int* p, int* q);

/*@
  predicate sorted(int* a, integer b, integer e) =
    \forall integer i, j; b <= i <= j < e ==> a[i] <= a[j];
*/

/*@
  requires \valid(a + (beg .. end-1));
  requires beg < end;
  assigns  a[beg .. end-1];
  ensures sorted(a, beg, end);
*/
void sort(int* a, size_t beg, size_t end){
  /* @ // add invariant */
  for(size_t i = beg ; i < end ; ++i){
    size_t imin = min_idx_in(a, i, end);
    swap(&a[i], &a[imin]);
  }
}
