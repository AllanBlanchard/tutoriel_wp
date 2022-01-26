/* run.config
   OPT:
*/

#include <stddef.h>

int* search(int* array, size_t length, int element){
  for(size_t i = 0; i < length; i++)
    if(array[i] == element) return &array[i];
  return NULL;
}
