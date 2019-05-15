#include <stdlib.h>
#include <limits.h>

/*@
  requires \valid_read(a) && \valid_read(b);
  
  assigns  \nothing ;

  ensures  \result == *a || \result == *b ;
  
  behavior is_b:
    assumes *a < *b ;
    ensures \result == *b ;

  behavior is_a:
    assumes *a > *b ;
    ensures \result == *a ;

  behavior is_both:
    assumes *a == *b ;
    ensures \result == *a == *b ;

  complete behaviors ;
  disjoint behaviors ;
*/
int max_ptr(int* a, int* b){
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
