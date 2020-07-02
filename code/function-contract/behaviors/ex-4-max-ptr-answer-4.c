#include <stdlib.h>
#include <limits.h>

/*@
  requires a == NULL || \valid_read(a) ;
  requires b == NULL || \valid_read(b);
  
  assigns  \nothing ;

  ensures  \result == INT_MIN || \result == *a || \result == *b ;
  
  behavior both_null:
    assumes a == NULL && b == NULL ;
    ensures \result == INT_MIN ;

  behavior a_null:
    assumes a == NULL && b != NULL ;
    ensures \result == *b ;

  behavior b_null:
    assumes a != NULL && b == NULL ;
    ensures \result == *a ;

  behavior is_a:
    assumes a != NULL && b != NULL && *a >= *b ;
    ensures \result == *a ;

  behavior is_b:
    assumes a != NULL && b != NULL && *a <  *b ;
    ensures \result == *b ;

  complete behaviors ;
  disjoint behaviors ;
*/
int max_ptr(int* a, int* b){
  if(!a && !b) return INT_MIN ;
  if(!a) return *b ;
  if(!b) return *a ;  
  return (*a < *b) ? *b : *a ;
}

extern int h ;

int main(){
  h = 42 ;

  int a = 24 ;
  int b = 42 ;

  int x = max_ptr(&a, &b) ;
  
  //@ assert x == 42 ;
  //@ assert h == 42 ;
}
