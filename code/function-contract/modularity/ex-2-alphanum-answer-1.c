/*@
  assigns \nothing ;
  ensures \result <==> 'a' <= c <= 'z' ;
*/
int is_lower_alpha(char c){
  return 'a' <= c && c <= 'z' ;
}

/*@
  assigns \nothing ;
  ensures \result <==> 'A' <= c <= 'Z' ;
*/
int is_upper_alpha(char c){
  return 'A' <= c && c <= 'Z' ;
}

/*@
  assigns \nothing ;
  ensures \result <==> '1' <= c <= '9' ;
*/
int is_digit(char c){
  return '1' <= c && c <= '9' ;
}

/*@
  assigns \nothing ;
  ensures 
  \result <==> (
    ('a' <= c <= 'z') ||
    ('A' <= c <= 'Z') ||
    ('1' <= c <= '9')
  ) ;
*/
int is_alpha_num(char c){
  return
    is_lower_alpha(c) || 
    is_upper_alpha(c) ||
    is_digit(c) ;
}
