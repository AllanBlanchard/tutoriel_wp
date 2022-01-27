/* run.config
   STDOPT:+"-wp-no-rte"
*/

/*@
  predicate rectangle{L}(integer c1, integer c2, integer h) =
    c1 * c1 + c2 * c2 == h * h ;
*/

/*@
  requires \separated(x, y, z);
  requires 3 <= *x <= 5 ;
  requires 4 <= *y <= 5 ;
  requires *z <= 5 ;
  requires *x+2 == *y+1 == *z ;
*/
void exercise(int* x, int* y, int* z){
  //@ assert rectangle(3* (*x), 3* (*y), 3* (*z));
  //@ ghost L: ;

  *x += 2 * (*x) ;
  *y += *y ;
  *y += (*y / 2);
  *z = 3 * (*z) ;

  //@ assert *x == \at(3* (*x), L) ;
  //@ assert *y == \at(3* (*y), L) ;
  //@ assert *z == \at(3* (*z), L);
  //@ assert rectangle(*x, *y, *z);
}
