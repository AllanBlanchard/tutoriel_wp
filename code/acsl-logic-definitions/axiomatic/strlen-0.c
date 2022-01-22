/* run.config
   DONTRUN:
*/

#include <stddef.h>

size_t strlen(char const *s){
  size_t i = 0 ;
  while(s[i] != '\0'){
    ++i;
  }
  return i ;
}
