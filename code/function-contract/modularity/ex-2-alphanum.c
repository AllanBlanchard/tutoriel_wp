/* run.config
   DONTRUN:
*/

int is_alpha_num(char c){
  return
    is_lower_alpha(c) ||
    is_upper_alpha(c) ||
    is_digit(c) ;
}
