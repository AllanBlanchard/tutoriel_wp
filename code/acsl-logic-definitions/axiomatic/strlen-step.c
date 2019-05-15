#include <stddef.h>
#include <limits.h>

/*@
  axiomatic StrLen {
    logic integer strlen(char * s) reads s[0 .. ] ;
  }
*/

/*@
  predicate valid_read_string(char * s) =
    \valid_read(s + (0 .. strlen(s))) ;
*/

/*@
  requires valid_read_string(s) ; 
  assigns \nothing ;
  ensures \result == strlen(s) ;
*/
size_t strlen(char const *s)
{
  size_t i = 0 ;
  /*@
    loop invariant 0 <= i <= strlen(s) ;
    loop assigns i ;
    loop variant strlen(s) - i ;
  */
  while(s[i] != '\0'){
    ++i;
  }
  return i ;
}
