#include <stddef.h>
#include <limits.h>

/*@
  requires \valid_read(array + (0 .. length-1));

  terminates \true ;
  decreases length ;

  assigns  \nothing;

  behavior in:
    assumes \exists unsigned off ; 0 <= off < length && array[off] == element;
    ensures 0 <= \result < length && array[\result] == element;

  behavior notin:
    assumes \forall unsigned off ; 0 <= off < length ==> array[off] != element;
    ensures \result == UINT_MAX;

  disjoint behaviors;
  complete behaviors;
*/
unsigned search(int* array, unsigned length, int element){
  if(length == 0) return UINT_MAX ;
  if(array[length-1] == element) return length - 1 ;
  else return search(array, length-1, element);
}
