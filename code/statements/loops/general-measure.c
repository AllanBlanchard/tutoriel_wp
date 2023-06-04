/* run.config
   STDOPT:
   OPT: -wp -wp-prop @variant -wp-print -wp-gen
*/

/*@ ensures \result >= 0;
    assigns \nothing ; */
int positive(void);

struct pair { int x, y ; };

/*@ predicate lexico(struct pair p1, struct pair p2) =
      p1.x > p2.x && p1.x >= 0 ||
      p1.x == p2.x && p1.y > p2.y && p1.y >= 0 ;
*/

//@ requires p.x >= 0 && p.y >= 0;
void f(struct pair p) {
  /*@ loop invariant p.x >= 0 && p.y >= 0;
      loop assigns p ;
      loop variant p for lexico;
  */
  while (p.x > 0 && p.y > 0) {
    if (positive()) {
      p.x--;
      p.y = positive();
    }
    else p.y--;
  }
}
