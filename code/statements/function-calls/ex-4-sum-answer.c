/* run.config
   STDOPT:+"-wp-no-rte"
*/

/*@ terminates \true ;
    decreases lst - fst ; */
int sum(int fst, int lst, int acc){
  if (fst >= lst) return acc ;
  else return sum(fst+1, lst, fst+acc) ;
}
