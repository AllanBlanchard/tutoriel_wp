/*@
  axiomatic A_all_zeros{
    predicate zeroed{L}(int* a, integer b, integer e) ;

    axiom zeroed_empty{L}:
      \forall int* a, integer b, e; b >= e ==> zeroed{L}(a,b,e);
      
    axiom zeroed_range{L}:
      \forall int* a, integer b, e; b < e ==>
        zeroed{L}(a,b,e-1) && a[e-1] == 0 <==> zeroed{L}(a,b,e);
  }
*/

#include <stddef.h>

/*@
  requires length > 10 ;
  requires \valid(array + (0 .. length-1));
  requires zeroed(array,0,length);
  assigns  array[0 .. length-1];
  ensures  zeroed(array,0,length);
*/
void bad_function(int* array, size_t length){
  array[5] = 42 ;
}

