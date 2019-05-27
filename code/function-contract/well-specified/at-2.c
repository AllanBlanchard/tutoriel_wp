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

/*@ requires x + 2 != p ; */
void example_4(int* x, int* p){
  *p = 2 ;
  //@ assert x[2]  == \at(x[2], Pre) ;
  //@ assert x[*p] == \at(x[*p], Pre) ;
}
