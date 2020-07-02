/*@
  requires \valid(a) && \valid(b);
  assigns  *a, *b ;
  ensures  \old(*a) < \old(*b)  ==> *a == \old(*b) && *b == \old(*a) ;
  ensures  \old(*a) >= \old(*b) ==> *a == \old(*a) && *b == \old(*b) ;
*/
void max_ptr(int* a, int* b){
  if(*a < *b){
    int tmp = *b ;
    *b = *a ;
    *a = tmp ;
  }
}

extern int h ;

int main(){
  h = 42 ;

  int a = 24 ;
  int b = 42 ;

  max_ptr(&a, &b) ;

  //@ assert a == 42 && b == 24 ;
  //@ assert h == 42 ;
}
