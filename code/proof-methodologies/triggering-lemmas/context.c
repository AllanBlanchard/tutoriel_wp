/* run.config
   STDOPT:+"-wp-no-rte -wp-msg-key state -wp-print"
*/

/*@
  predicate rectangle{L}(integer c1, integer c2, integer h) =
    c1 * c1 + c2 * c2 == h * h ;
*/

/*@
  requires \separated(x, y , z);
  requires 3 <= *x <= 5 ;
  requires 4 <= *y <= 5 ;
  requires *z <= 5 ;
  requires *x+2 == *y+1 == *z ;
*/
void example_1(int* x, int* y, int* z){
  //@ assert rectangle(*x, *y, *z);
  //@ assert rectangle(2* (*x), 2* (*y), 2* (*z));
}


/*@
  requires \separated(x, y , z);
  requires 3 <= *x <= 5 ;
  requires 4 <= *y <= 5 ;
  requires *z <= 5 ;
  requires *x+2 == *y+1 == *z ;
*/
void example_1_p(int* x, int* y, int* z){
  goto next;
  //@ assert rectangle(*x, *y, *z);
 next: ;
  //@ assert rectangle(2* (*x), 2* (*y), 2* (*z));
}


/*@
  requires \separated(x, y , z);
  requires 3 <= *x <= 5 ;
  requires 4 <= *y <= 5 ;
  requires *z <= 5 ;
  requires *x+2 == *y+1 == *z ;
*/
void example_2(int* x, int* y, int* z){
  *x += 3 ;
  *y += 4 ;
  *z += 5 ;

  //@ assert rectangle(*x, *y, *z);
}

/*@
  requires \separated(x, y , z);
  requires 3 <= *x <= 5 ;
  requires 4 <= *y <= 5 ;
  requires *z <= 5 ;
  requires *x+2 == *y+1 == *z ;
*/
void example_3(int* x, int* y, int* z){
  //@ assert rectangle(2* (*x), 2* (*y), 2* (*z));
  //@ ghost L: ;

  *x += 3 ;
  *y += 4 ;
  *z += 5 ;

  //@ assert *x == \at(2* (*x), L) ;
  //@ assert *y == \at(2* (*y), L) ;
  //@ assert *z == \at(2* (*z), L);
  //@ assert rectangle(*x, *y, *z);
}
