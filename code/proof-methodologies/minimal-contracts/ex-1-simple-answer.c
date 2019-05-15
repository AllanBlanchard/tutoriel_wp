#include <limits.h>

/*@
  requires \valid(a) && \valid(b) ;
  assigns *a, *b ;
*/
void max_ptr(int* a, int* b){
  if(*a < *b){
    int tmp = *b ;
    *b = *a ;
    *a = tmp ;
  }
}

/*@
  requires \valid(a) && \valid(b) ;
  assigns *a, *b ;
*/
void min_ptr(int* a, int* b){
  max_ptr(b, a);
}

/*@
  requires \valid(a) && \valid(b) && \valid(c) ;
  assigns *a, *b, *c ;
*/
void order_3_inc_min(int* a, int* b, int* c){
  min_ptr(a, b) ;
  min_ptr(a, c) ;
  min_ptr(b, c) ;
}

/*@
  requires \valid(a) && \valid_read(b) ;
  requires INT_MIN <= *a + *b <= INT_MAX ;
  assigns  *a;
*/
void incr_a_by_b(int* a, int const* b){
  *a += *b;
}
