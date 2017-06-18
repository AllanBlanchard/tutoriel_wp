# Consequence rule

It can sometimes be useful to strengthen a postcondition or
to weaken a precondition.
If the former will often be established by us to facilitate the work of the
prover, the second is more often verified by the tool as the result of computing
the weakest precondition.

The inference rule of Hoare logic is the following:

->$\dfrac{P \Rightarrow WP \quad \{WP\}\quad c\quad \{SQ\} \quad SQ \Rightarrow Q}{\{P\}\quad c \quad \{Q\}}$<-

(We remark that the premises here are not only Hoare triples but also formulas
to verify.)

For example, if our post-condition is too complex, it may generate a weaker
precondition that is, however, too complicated, thus making the work of provers
more difficult. We can then create a simpler intermediate postcondition $SQ$,
that is, however, stricter and implies the real postcondition.
This is the part $SQ \Rightarrow Q$.

Conversely, the calculation of the precondition will usually generate a
complicated and often weaker formula than the precondition we want to accept as
input. In this case, it is our tool that will check the implication between
what we want and what is necessary for our code to be valid.
Th is is the part $P \Rightarrow WP$.

We can illustrate this with the following code. Note that here the code could
be proved by WP without the weakening and strengthening of properties because
the code is very simple, it is just to illustrate the rule of consequence.


```c
/*@
  requires P: 2 <= a <= 8;
  ensures  Q: 0 <= \result <= 100 ;
  assigns  \nothing ;
*/
int constrained_times_10(int a){
  //@ assert P_imply_WP: 2 <= a <= 8 ==> 1 <= a <= 9 ;
  //@ assert WP:         1 <= a <= 9 ;

  int res = a * 10;

  //@ assert SQ:         10 <= res <= 90 ;
  //@ assert SQ_imply_Q: 10 <= res <= 90 ==> 0 <= res <= 100 ;

  return res;
}
```
(Note: We have omitted here the control of integer overflow.)

Here we want to have a result between 0 and 100. But we know that the code will
not produce a result outside the bounds of 10 and 90. So we strengthen the
postcondition with an assertion that at the end `res`, the result, is between
0 and 90. The calculation of the weakest precondition of this property together
with the assignment `res = 10 * a` yields a weaker precondition `1 <= a <= 9`
and we know that `2 < = a <= 8` gives us the desired guarantee.

When there are difficulties to carry out a proof on more complex code, then it
is often helpful to write assertions that produce stronger, yet easier to
verify, postconditions. Note that in the previous code, the lines `P_imply_WP`
and` SQ_imply_Q` are never used because this is the default reasoning of WP.
They are just here for illustrating the rule.

# Constant rule (???)

Certain sequences of instructions may concern and involve different variables.
Thus, we may initialize and manipulate a certain number of variables, begin to
use some of them for a time, before using other variables.
When this happens, we want our tool to be concerned only with variables that
are susceptible to change in order to obtain the simplest possible properties.

The rule of inference that defines this reasoning is the following:

-> $\dfrac{\{P\}\quad c\quad \{Q\}}{\{P \wedge R\}\quad c\quad \{Q \wedge R\}}$ <-

where $c$ does not modify any input variable in $R$.
In other words: "To check the triple, let's get rid of the parts of the formula
that involves variables that are not influence by $c$ and prove the new triple."
However, we must be careful not to delete too much information, since this could
mean that we are not able to prove our properties.

As an example,let us consider the following code (here gain, we ignore
potential integer overflows):


```c
/*@
  requires a > -99 ;
  requires b > 100 ;
  ensures  \result > 0 ;
  assigns  \nothing ;
*/
int foo(int a, int b){
  if(a >= 0){
    a++ ;
  } else {
    a += b ;
  }
  return a ;
}
```

If we look at the code of the `if` block, we notice that it does not use the
variable `b`. Thus, we can completely omit the properties about `b` in order to
prove that `a` will be strictly greater than 0 after the execution of the block:

```c
/*@
  requires a > -99 ;
  requires b > 100 ;
  ensures  \result > 0 ;
  assigns  \nothing ;
*/
int foo(int a, int b){
  if(a >= 0){
    //@ assert a >= 0; // no mentioning of b
    a++ ;
  } else {
    a += b ;
  }
  return a ;
}
```

On the other hand, in the `else` block, even if `b` were not modified,
formulating properties only about `a` would make our proof impossible (???as humans???).
The code would be:

```c
/*@
  requires a > -99 ;
  requires b > 100 ;
  ensures  \result > 0 ;
  assigns  \nothing ;
*/
int foo(int a, int b){
  if(a >= 0){
    //@ assert a >= 0; // no mentioning of b
    a++ ;
  } else {
    //@ assert a < 0 && a > -99 ; // no mentioning of b
    a += b ;
  }
  return a ;
}
```

In the `else` block, knowing that` a` lies between -99 and 0, but knowing
nothing about `b`, we could hardly know if the operation `a + = b` produces a
result that is greater than 0.

The WP plug-in will, of course, prove the function without problems, since it
produces by itself the properties that are necessary for the proof.
In fact, the analysis which variables are necessary or not (and, consequently,
the application of the constant rule) is conducted directly by WP.

Let us finally remark that the constant rule is an instance of the consequence
rule:

->$\dfrac{P \wedge R \Rightarrow P \quad \{P\}\quad c\quad \{Q\} \quad Q \Rightarrow Q \wedge R}{\{P \wedge R\}\quad c\quad \{Q \wedge R\}}$ <-

If the variables of $R$ have not been modified by the operation
(which, on the other hand, may modify the variables of $P$ to produce $Q$),
then the properties $P \ wedge R \ Rightarrow P$ and
$Q \ Rightarrow Q \ wedge R$ hold.
