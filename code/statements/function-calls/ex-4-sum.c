/* run.config
   OPT:
*/

int sum(int fst, int lst, int acc){
  if (fst == lst) return acc ;
  else return sum(fst+1, lst, fst+acc) ;
}
