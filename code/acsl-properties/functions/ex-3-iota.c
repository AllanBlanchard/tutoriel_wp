/* run.config
   DONTRUN:
*/

#include <limits.h>
#include <stddef.h>

void iota(int* array, size_t len, int value){
  if(len){
    array[0] = value ;

    for(size_t i = 1 ; i < len ; i++){
      array[i] = array[i-1]+1 ;
    }
  }
}
