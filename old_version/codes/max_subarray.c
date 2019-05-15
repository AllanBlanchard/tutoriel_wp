#include <stddef.h>

/*@
  axiomatic Sum_array{
  logic integer sum(int* array, integer begin, integer end) reads array[begin .. end];
  axiom empty: 
  \forall int* a, integer b, e; b >= e ==> sum(a,b,e) == 0;
  axiom range:
  \forall int* a, integer b, e; b < e ==> sum(a,b,e) == sum(a,b,e-1)+a[e-1];
  }
*/

/*@ 
  requires \valid(a+(0..len-1));
  assigns \nothing;
  ensures \forall integer l, h;  0 <= l <= h <= len ==> sum(a,l,h) <= \result;
  ensures \exists integer l, h;  0 <= l <= h <= len &&  sum(a,l,h) == \result;
*/
int max_subarray(int *a, size_t len) {
  int max = 0;
  int cur = 0;
  //@ ghost size_t cur_low = 0; 
  //@ ghost size_t low = 0;
  //@ ghost size_t high = 0; 

  /*@ 
    loop invariant BOUNDS: low <= high <= i <= len && cur_low <= i;
    
    loop invariant REL :   cur == sum(a,cur_low,i) <= max == sum(a,low,high);
    loop invariant POST:   \forall integer l;    0 <= l <= i      ==> sum(a,l,i) <= cur;
    loop invariant POST:   \forall integer l, h; 0 <= l <= h <= i ==> sum(a,l,h) <= max;
   
    loop assigns i, cur, max, cur_low, low, high;
    loop variant len - i; 
  */
  for(size_t i = 0; i < len; i++) {
    cur += a[i];
    if (cur < 0) {
      cur = 0;
      /*@ ghost cur_low = i+1; */
    }
    if (cur > max) {
      max = cur;
      /*@ ghost low = cur_low; */
      /*@ ghost high = i+1; */
    }
  }
  return max;
}
