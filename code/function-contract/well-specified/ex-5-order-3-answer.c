/*@
  requires \valid(a) && \valid(b) && \valid(c) ;
  requires \separated(a, b, c);
  assigns *a, *b, *c ;
  ensures *a <= *b <= *c ;
  ensures *a == \old(*a) || *a == \old(*b) || *a == \old(*c) ;
  ensures *b == \old(*a) || *b == \old(*b) || *b == \old(*c) ;
  ensures *c == \old(*a) || *c == \old(*b) || *c == \old(*c) ;
  ensures { *a, *b, *c } == \old({ *a, *b, *c }) ;
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
