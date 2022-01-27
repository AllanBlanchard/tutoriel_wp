/* run.config
   STDOPT:#"-warn-unsigned-overflow -warn-unsigned-downcast"
*/

#include <stddef.h>

/*@
  requires beg < end ;
  requires \valid_read(a+(beg .. end-1)) ;
  assigns \nothing ;
  ensures beg <= \result < end ;
*/
size_t min_idx_in(int* a, size_t beg, size_t end){
  size_t min_i = beg;
  /*@
    loop invariant beg+1 <= i <= end ;
    loop invariant beg <= min_i < end ;
    loop assigns i, min_i ;
  */
  for(size_t i = beg+1; i < end; ++i){
    if(a[i] < a[min_i]) min_i = i;
  }
  return min_i;
}

/*@
  requires \valid(p) && \valid(q);
  assigns *p, *q;
*/
void swap(int* p, int* q){
  int tmp = *p; *p = *q; *q = tmp;
}

/*@
  requires beg <= end ;
  requires \valid(a+(beg .. end-1)) ;
  assigns a[beg .. end-1] ;
*/
void sort(int* a, size_t beg, size_t end){
  /*@
    loop invariant beg <= i <= end ;
    loop assigns i, a[beg .. end-1] ;
  */
  for(size_t i = beg ; i < end ; ++i){
    size_t imin = min_idx_in(a, i, end);
    swap(&a[i], &a[imin]);
  }
}
