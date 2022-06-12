/* run.config
   OPT:
*/

#include <stddef.h>
#include <limits.h>

unsigned search(int* array, unsigned length, int element){
  if(length == 0) return UINT_MAX ;
  if(array[length-1] == element) return length - 1 ;
  else return search(array, length-1, element);
}
