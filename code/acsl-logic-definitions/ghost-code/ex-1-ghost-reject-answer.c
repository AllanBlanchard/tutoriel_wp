#include <stddef.h>
#include <limits.h>

/*@
  assigns \nothing;
  ensures \result == a || \result == b ;
  ensures \result >= a && \result >= b ;
*/
int max(int a, int b){
  int r = INT_MAX;
  // Ghost code write 'r' which is non-ghost
  // It hides the fact that the function just returns INT_MAX
  //@ ghost r = (a > b) ? a : b ;
  return r ;
}

/*@
  requires \valid(a) && \valid(b);
  assigns *a, *b;
  ensures *a == \old(*b) && *b == \old(*a);
*/
void swap(int* a, int* b){
  int tmp = *a ;
  *a = *b ;
  // Ghost code casts a pointer to non-ghost in a pointer to ghost
  //@ ghost int \ghost* ptr = b ;
  // Thus, it can be used to hide that *b is not updated correctly
  //@ ghost *ptr = tmp ;
}

/*@
  requires \valid(a+(0 .. len-1));
  assigns  \nothing ;
  ensures \result <==> (\forall integer i ; 0 <= i < len ==> a[i] == 0);
*/
int null_vector(int* a, size_t len){
  //@ ghost int value = len ;
  /*@ loop invariant 0 <= i <= len ;
    loop invariant \forall integer j ; 0 <= j < i ==> a[j] == 0 ;
    loop assigns i ;
    loop variant len-i ;
  */
  for(size_t i = 0 ; i < len ; ++i)
    if(a[i] != 0) return 0;
	// This loop does not terminate thus it hides the fact that the
	// function does not return the right value when all cells are
	// 0.
  /*@ ghost 
    /@ loop assigns \nothing ; @/
    while(value >= len);
  */
  return 0;
}
