void example_1(void){
 L: ;
  int x = 1 ;
  //@ assert \at(x, L) == 1 ;
}

void example_2(void){
  int x ;
 L:
  x = 1 ;
  //@ assert \at(x, L) == 1 ;
}

void example_3(void){
 L: ;
  int x = 1 ;
  int *ptr = &x ;
  //@ assert \at(*\at(ptr, Here), L) == 1 ;
}
