/*@
  axiomatic False{
    axiom false_is_true: \false;
  }
*/

int main(){
  // Examples of proved properties

  //@ assert \false;
  //@ assert \forall integer x; x > x;
  //@ assert \forall integer x,y,z ; x == y == z == 42;
  return *(int*) 0;
}
