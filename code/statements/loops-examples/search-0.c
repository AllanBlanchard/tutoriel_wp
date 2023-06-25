/* run.config
   OPT:
*/

#include <stddef.h>

/*@
  requires \valid_read(array + (0 .. length-1));

  assigns  \nothing;

  behavior notin:
    assumes \forall size_t off ; 0 <= off < length ==> array[off] != element;
    ensures \result == NULL;

  behavior in:
    assumes \exists size_t off ; 0 <= off < length && array[off] == element;
    ensures array <= \result < array+length && *\result == element;

  disjoint behaviors;
  complete behaviors;
*/
int* search(int* array, size_t length, int element){
  for(size_t i = 0; i < length; i++)
    if(array[i] == element) return &array[i];
  return NULL;
}
