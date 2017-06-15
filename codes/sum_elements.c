#include <stddef.h>

/*@
  axiomatic Sum_array{
  logic integer sum_of(int* array, integer begin, integer end) reads array[begin .. end];
  axiom empty: 
  \forall int* a, integer b, e; b >= e ==> sum_of(a,b,e) == 0;
  axiom range:
  \forall int* a, integer b, e; b < e ==> sum_of(a,b,e) == sum_of(a,b,e-1)+a[e-1];
  }
*/

int sum(int* array, size_t length){
  int res = 0;
  /*@
    loop invariant 0 <= i <= length;
    loop invariant res == sum_of(array,0,i);
    loop assigns res, i;
    loop variant length - i ;
  */
  for(size_t i = 0; i< length; ++i)
    res += array[i];
  return res;
}
