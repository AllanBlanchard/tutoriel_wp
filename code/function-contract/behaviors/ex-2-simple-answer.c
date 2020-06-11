enum Kind { VOWEL, CONSONANT };

/*@
  requires 'a' <= c <= 'z' ;
  assigns \nothing;
  behavior vowel:
    assumes c \in { 'a', 'e', 'i', 'o', 'u', 'y' };
    ensures \result == VOWEL;
  behavior consonant:
    assumes ! (c \in { 'a', 'e', 'i', 'o', 'u', 'y' });
    ensures \result == CONSONANT;
  complete behaviors;
  disjoint behaviors;
*/
enum Kind kind_of_letter(char c){
  if(c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'y')
    return VOWEL;
  else
    return CONSONANT;
}

/*@
  assigns \nothing;
  ensures 1 <= \result <= 4;

  behavior I:
    assumes x >= 0 && y >= 0;
    ensures \result == 1;
 
  behavior II:
    assumes x <  0 && y >= 0;
    ensures \result == 2;

  behavior III:
    assumes x <  0 && y <  0;
    ensures \result == 3;
  
  behavior IV:
    assumes x >= 0 && y <  0;
    ensures \result == 4;

  complete behaviors;
  disjoint behaviors;
*/ 
int quadrant(int x, int y){
  if(x >= 0){
    if(y >= 0) return 1;
    else return 4;
  } else{
    if(y >= 0) return 2;
    else return 3;
  }
}
