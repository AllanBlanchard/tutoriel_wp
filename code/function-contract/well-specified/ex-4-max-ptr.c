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
