/*@
  predicate one_of{L}(integer i, int *a, int *b, int *c) =
    \exists int* p ; p \in { a, b, c } && \at(*p, L) == i ;
*/
/*@
  predicate permutation{L1, L2}(int *a, int *b, int *c) =
    \at(*{ a, b, c }, L1) == \at(*{ a, b, c }, L2) ;
*/

/*@
  requires \valid(a) && \valid(b) && \valid(c) ;
  requires \separated(a, b, c);
  assigns *a, *b, *c ;
  ensures *a <= *b <= *c ;
  ensures one_of{Pre}(*a, a, b, c);
  ensures one_of{Pre}(*b, a, b, c);
  ensures one_of{Pre}(*c, a, b, c);
  ensures permutation{Pre, Post}(a, b, c) ;
*/
void order_3(int* a, int* b, int* c){
  if(*a > *b){
    int tmp = *b ; *b = *a ; *a = tmp ;
  }
  if(*a > *c){
    int tmp = *c ; *c = *a ; *a = tmp ;
  }
  if(*b > *c){
    int tmp = *b ; *b = *c ; *c = tmp ;
  }
}

void test(){
  int a = 5, b = 3, c = 4 ;
  order_3(&a, &b, &c) ;
  //@ assert a == 3 && b == 4 && c == 5 ;
}
