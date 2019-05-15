/*@
  requires \valid(a) && \valid_read(b) ;
  requires \separated(a, b) ;

  assigns *a ;

  ensures *b == \old(*b);
  
  behavior reset:
    assumes *b ;
    ensures *a == 0 ;

  behavior const:
    assumes ! *b ;
    ensures *a == \old(*a) ;

  complete behaviors ;
  disjoint behaviors ;
*/
void reset_1st_if_2nd_is_true(int* a, int const* b){
  if(*b) *a = 0 ;
}

int main(){
  int a = 5 ;
  int x = 0 ;

  reset_1st_if_2nd_is_true(&a, &x);
  //@ assert a == 5 ;
  //@ assert x == 0 ;
  
  int const b = 1 ;

  reset_1st_if_2nd_is_true(&a, &b);
  //@ assert a == 0 ;
  //@ assert b == 1 ;
}
