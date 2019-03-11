enum Kind { LOWER, UPPER, DIGIT, OTHER } ;

/*@
  predicate lower(char c) = 'a' <= c <= 'z' ;
  predicate upper(char c) = 'A' <= c <= 'Z' ;
  predicate digit(char c) = '0' <= c <= '9' ;
*/

/*@
  assigns \nothing ;
  ensures \result <==> lower(c) ;
*/
int is_lower_alpha(char c){
  return 'a' <= c && c <= 'z' ;
}

/*@
  assigns \nothing ;
  ensures \result <==> upper(c) ;
*/
int is_upper_alpha(char c){
  return 'A' <= c && c <= 'Z' ;
}

/*@
  assigns \nothing ;
  ensures \result <==> digit(c) ;
*/
int is_digit(char c){
  return '0' <= c && c <= '9' ;
}

/*@
  assigns \nothing ;
  behavior lower:
    assumes lower(c);
    ensures \result == LOWER ;

  behavior upper:
    assumes upper(c) ;
    ensures \result == UPPER ;

  behavior digit:
    assumes digit(c) ;
    ensures \result == DIGIT ;

  behavior other:
    assumes !(lower(c) || upper(c) || digit(c)) ;
    ensures \result == OTHER ;

  complete behaviors ;
  disjoint behaviors ;
*/
enum Kind character_kind(char c){
  if(is_lower_alpha(c)) return LOWER ;
  if(is_upper_alpha(c)) return UPPER ;
  if(is_digit(c))       return DIGIT ;
  return OTHER ;
}
