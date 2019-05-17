#include <stddef.h>
#include <limits.h>

/*@
  axiomatic StrLen {
    logic integer strlen(char * s) reads s[0 .. ] ;
    
    axiom pos_or_nul{L}:
      \forall char* s, integer i ;
        (0 <= i && (\forall integer j ; 0 <= j < i ==> s[j] != '\0') && s[i] == '\0') ==>
	  strlen(s) == i ;

    axiom no_end{L}:
      \forall char* s ;
        (\forall integer i ; 0 <= i ==> s[i] != '\0') ==> strlen(s) < 0 ;

    axiom index_of_strlen{L}:
      \forall char* s ;
        strlen(s) >= 0 ==> s[strlen(s)] == '\0' ;

    axiom before_strlen{L}:
      \forall char* s ;
        strlen(s) >= 0 ==> (\forall integer i ; 0 <= i < strlen(s) ==> s[i] != '\0') ;
  }
*/

/*@
  predicate valid_read_string(char * s) =
    strlen(s) >= 0 && \valid_read(s + (0 .. strlen(s))) ;
*/

/*@
  requires valid_read_string(s) && strlen(s) <= UINT_MAX ;
  assigns \nothing ;
  ensures \result == strlen(s) ;
*/
size_t strlen(char const *s)
{
  size_t i = 0 ;
  /*@
    loop invariant 0 <= i <= strlen(s) ;
    loop invariant \forall integer j ; 0 <= j < i ==> s[j] != '\0' ;
    loop assigns i ;
    loop variant strlen(s) - i ;
  */
  while(s[i] != '\0'){
    ++i;
  }
  return i ;
}


/*
int main(){
  char const s[] = "CRABE" ;
  size_t x = strlen(s);
  //@ assert x == 5 ;
}
*/
