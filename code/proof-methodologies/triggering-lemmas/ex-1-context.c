/*@
  predicate rectangle{L}(integer c1, integer c2, integer h) =
    c1 * c1 + c2 * c2 == h * h ;
*/

/*@
  requires \separated(x, y , z);
  requires 3 <= *x <= 5 ;
  requires 3 <= *y <= 5 ;
  requires 2 <= *z <= 5 ;
  requires *x+2 == *y+1 == *z ;
*/
void exercise(int* x, int* y, int* z){
  *x += 2 * (*x) ;
  *y += *y ;
  *y += (*y / 2);
  *z = 3 * (*z) ;
  //@ assert rectangle(*x, *y, *z);
}
