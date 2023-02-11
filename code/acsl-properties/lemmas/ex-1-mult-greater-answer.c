/* run.config
   DEPS: @PTEST_DEPS@ @PTEST_DIR@/@PTEST_NAME@.@PTEST_NUMBER@.session@PTEST_CONFIG@/interactive/*.v
   STDOPT:+"-wp-prover alt-ergo,coq -wp-session @PTEST_DIR@/@PTEST_NAME@.@PTEST_NUMBER@.session@PTEST_CONFIG@"
*/
/*@
  lemma mult_greater:
    \forall integer x, y, z ; x >= 0 ==> y <= z ==> x * y <= x * z ;
*/
