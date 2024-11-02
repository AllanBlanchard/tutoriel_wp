/* run.config
   STDOPT:+"-wp-timeout 5"
*/

enum note { N500, N200, N100, N50, N20, N10, N5, N2, N1 };
int const values[] = { 500, 200, 100, 50, 20, 10, 5, 2, 1 };

/*@
  requires N500 <= n <= N1;
  requires \valid(rest) && *rest >= 0 ;
  assigns *rest;
  ensures \result == \old(*rest)/values[n];
  ensures \old(*rest) == *rest + \result * values[n] ;
*/
int remove_max_notes(enum note n, int* rest){
  int num = (*rest)/values[n];
  (*rest) -= num * values[n];
  return num;
}

/*@
  requires \valid(change+(0..8));
  requires amount >= 0 && received >= 0;
  assigns  change[0 .. 8];

  behavior not_enough:
    assumes amount > received ;
    ensures \result == -1;

  behavior change:
    assumes amount <= received ;
    ensures \result == 0;
    ensures
      received - amount ==
          change[N500] * values[N500]
        + change[N200] * values[N200]
        + change[N100] * values[N100]
        + change[N50]  * values[N50]
        + change[N20]  * values[N20]
        + change[N10]  * values[N10]
        + change[N5]   * values[N5]
        + change[N2]   * values[N2]
        + change[N1]   * values[N1];
    ensures
         change[N1]   * values[N1]   < values[N2]
      && change[N2]   * values[N2]   < values[N5]
      && change[N5]   * values[N5]   < values[N10]
      && change[N10]  * values[N10]  < values[N20]
      && change[N20]  * values[N20]  < values[N50]
      && change[N50]  * values[N50]  < values[N100]
      && change[N100] * values[N100] < values[N200]
      && change[N200] * values[N200] < values[N500];

  complete behaviors;
  disjoint behaviors;
*/
int make_change(int amount, int received, int change[9]){
  if(amount > received) return -1;

  int rest = received - amount ;

  change[N500] = remove_max_notes(N500, &rest);
  change[N200] = remove_max_notes(N200, &rest);
  change[N100] = remove_max_notes(N100, &rest);
  change[N50]  = remove_max_notes(N50,  &rest);
  change[N20]  = remove_max_notes(N20,  &rest);
  change[N10]  = remove_max_notes(N10,  &rest);
  change[N5]   = remove_max_notes(N5,   &rest);
  change[N2]   = remove_max_notes(N2,   &rest);
  change[N1]   = remove_max_notes(N1,   &rest);

  return 0;
}
