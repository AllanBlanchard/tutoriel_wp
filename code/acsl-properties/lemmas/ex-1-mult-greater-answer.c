/* run.config
   STDOPT:+"-wp-prover alt-ergo,coq -wp-session @PTEST_SUITE_DIR@/oracle@PTEST_CONFIG@/@PTEST_NAME@.session"
*/
/*@
  lemma mult_greater:
    \forall integer x, y, z ; x >= 0 ==> y <= z ==> x * y <= x * z ;
*/
