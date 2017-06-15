/*@
  logic integer ax_b(integer a, integer x, integer b) =
    a * x + b;
*/

/*@ 
  assigns \nothing ;
  ensures \result == ax_b(3,x,4); 
*/
int function(int x){
  return 3*x + 4;
}
