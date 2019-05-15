#include <limits.h>

/*@ 
  requires INT_MIN <= *p + *q <= INT_MAX ;
  requires \valid_read(p) && \valid_read(q) && \valid(r) ;
  requires \separated(p, r);
  requires \separated(q, r);
  assigns *r ;
  ensures *r == *p + *q ;
*/
void add(int *p, int *q, int *r){
  *r = *p + *q ;
}

int main(){
  int a = 24 ;
  int b = 42 ;

  int x ;

  add(&a, &b, &x) ;
  //@ assert x == a + b ;
  //@ assert x == 66 ;

  add(&a, &a, &x) ;
  //@ assert x == a + a ;
  //@ assert x == 48 ;
}
