The goal of a function contract is to state the conditions under which the
function will execute. That is to say, what the function expect from the
caller to ensure that it will correctly behave: the precondition, the notion
of "correctly behave" being itself defined in the contract by the
postcondition.

These properties are expressed with ACSL, the syntax is relatively simple if
one have already developed in C language since it shares most of the syntax
of boolean expressions in C. However, it also provides:

- some logic constructs and connectors that do not exists in C, to ease the
  writing of specifications,
- built-in predicates to express properties that are useful about C
  programs (for example: a valid pointer),
- as well as some primitive types for the logic that are more general than
  primitive C types (for example: mathematical integer).

We will introduce along this tutorial a large part of the notations available
in ACSL.

ACSL specifications are introduced in our source code using annotations.
Syntactically, a function contract is integrated in the source code with
this syntax:

```c
/*@
  //contract
*/
void foo(int bar){

}
```

Notice the `@` at the beginning of the comment block, this indicates to
Frama-C that what follows are annotations and not a comment block that it
should simply ignore.

Now, let us have a look to the way we express contracts, starting with
postconditions, since it is what we want our function to do (we will later
see how to express precondition).

# Postcondition

The postcondition of a function is introduced with the clause `ensures`.
We will illustrate its use with the following function that returns the
absolute value of an input. One of its postconditions is that the result
(which is denoted with the keywork `\result`) is greater or equal to 0.

```c
/*@
  ensures \result >= 0;
*/
int abs(int val){
  if(val < 0) return -val;
  return val;
}
```

(Notice the `;` at the end of the line, exactly as we do in C).

But that it is not the only property to verify, we also need to specify
the general behavior of a function returning the absolute value. That is:
if the value is positive or 0, the function returns the same value, else
it returns the opposite of the value.

We can specify multiple postconditions, first by combining them with a
`&&` as we do in C, or by introducing a new `ensures` clause, as we
illustrate here:

```c
/*@
  ensures \result >= 0;
  ensures (val >= 0 ==> \result == val ) && 
          (val <  0 ==> \result == -val);
*/
int abs(int val){
  if(val < 0) return -val;
  return val;
}
```

This specification is the opportunity to present a very useful logic
connector provided by ACSL and that does not exist in C:
the implication $A \Rightarrow B$, that is written `A ==> B` in ACSL.
The truth table of the implication is the following:

$A$ | $B$ | $A \Rightarrow B$
----|-----|-------------------
$F$ | $F$ | $T$
$F$ | $T$ | $T$
$T$ | $F$ | $F$
$T$ | $T$ | $T$

That means that an implication $A \Rightarrow B$ is true in two cases:
either $A$ is false (and in this case, we do not check the value of $B$), or
$A$ is true and then $B$ must also be true. The idea finally being "I want to
know if when $A$ is true, $B$ also is. If $A$ is false, I don't care, I
consider that the complete formula is true".

Another available connector is the equivalence $A \Leftrightarrow B$ (written
`A <==> B` in ACSL), and it is stronger. It is conjunction of the implication
in both ways $(A \Rightarrow B) \wedge (B \Rightarrow A)$. This formula is
true in only two cases: $A$ and $B$ are both ture, or false (it can be seen as
the negation of the exclusive or).

[[information]]
| Let's give a quick reminder about all truth tables of usual logic connectors
| in first order logic ($\neg$ = `!`, $\wedge$ = `&&`, $\vee$ = `||`) :
|
| $A$ | $B$ | $\neg A$ | $A \wedge B$ | $A \vee B$ | $A \Rightarrow B$ | $A \Leftrightarrow B$
| ----|-----|----------|--------------|------------|-------------------|-----------------------
| $F$ | $F$ | $T$      | $F$          | $F$        | $T$               | $T$
| $F$ | $T$ | $T$      | $F$          | $T$        | $T$               | $F$
| $T$ | $F$ | $F$      | $F$          | $T$        | $F$               | $F$
| $T$ | $T$ | $F$      | $T$          | $T$        | $T$               | $T$

We can come back to our specification. As our files become longer and contains
a lot of specifications, if can be useful to name the properties we want to
verify. So, in ACSL, we can specify a name (without spaces) followed by a `:`,
before stating the property. It is possible to put multiple levels of names
to categorize our properties. For example, we could write this:

```c
/*@
  ensures positive_value: function_result: \result >= 0;
  ensures (val >= 0 ==> \result == val) && 
          (val < 0 ==> \result == -val);
*/
int abs(int val){
  if(val < 0) return -val;
  return val;
}
```

In most of this tutorial, we will not name the properties we want to prove,
since they will be generally quite simple and we will not have too many of
them, names would not give us much information.

We can copy and paste the function `abs` and its specification in a file
`abs.c` and use Frama-C to determine if the implementation is correct
against the specification. We can start the GUI of Frama-C (it is also
possible to use the command line interface of Frama-C but we will not use
it during this tutorial) by using this command line:

```bash
$ frama-c-gui
```

Or by opening it from the graphical environment. 

It is then possible to click on the button "Create a new session from 
existing C files", files to analyze can be selected by double-clicking it,
the OK button ending the selection. Then, adding other files will be done
by clicking Files > Source Files.

Notice that it is also possible to directly open file(s) from the terminal
command line passing them to Frama-C as parameter(s):

```bash
$ frama-c-gui abs.c
```

![The side panel gives the files and functions tree](https://zestedesavoir.com:443/media/galleries/2584/dab8888e-32fc-4856-bb87-4de884829822.png)

The window of Frama-C opens and in the panel dedicated to files and functions,
we can select the function `abs`. At each `ensures` line, we can see a blue
circle, it indicates that no verification has been attempted for these
properties.

We ask the verification of the code by right-clicking the name of the function
and "Prove function annotations by WP":

![Start the verification of ```abs``` with WP](https://zestedesavoir.com:443/media/galleries/2584/ed44f0d3-763f-423e-8a01-a9be7aace0d3.png)

We can see that blue circles become green bullets, indicating that the
specification is indeed ensured by the program. We can also prove properties
one by one by right-clicking on them and not on the name of the function.

But is our code really bug free ? WP gives us a way to ensure that a code
respects a specification, but it does not check for runtime errors (RTE). This
is provided by another plugin that we will use here and that is called RTE.
Its goal is to add, in the program, some controls to ensure that the program
cannot create runtime errors (integer overflow, invalid pointer dereferencing,
0 division, etc).

To active these controls, we check the box pointed by the screenshot (in the
WP panel). We can also ask Frama-C to add them in a function by right-clicking
on its name and then click "Insert RTE guards".

![Activate runtime error absence verification](https://zestedesavoir.com:443/media/galleries/2584/bae7515e-8841-4a27-9253-e1bf26eb0d81.png)

Finally, we execute the verification again (we can also click on the
"Reparse" button of the toolbar, it will deletes existing proofs).

We can then see that WP fails to prove the absence of arithmetic underflow
for the computation of `-val`. And, indeed, on our architectures,
`-INT_MIN` ($-2^{31}$) > `INT_MAX` ($2^{31}-1$).

![Incomplete proof of ```abs```](https://zestedesavoir.com:443/media/galleries/2584/ec869f49-9193-4896-a490-9549f256a639.png)

[[information]]
| We can notice that there exists an actual underflow risk, since our
| computers (for which the configuration is detected by Frama-C) use the
| [Two's complement](https://en.wikipedia.org/wiki/Two%27s_complement)
| implementation of integers, which do not defined the behavior of under and
| overflows.

Here, we can see another type of ACSL annotation. By the line
`//@ assert property ;`, we can ask the verification of property at a
particular program point. Here, RTE inserted for us, since we have to verify
that `-val` does not produce an underflow, but we can also add such an
assertion manually in the source code.

In this screenshot, we can see two new colors for our bullets: green+brown and
orange.

The green+brown color indicates that the proof has been produced but it
can depend on some properties that have not been verified.

If the proof has not been entirely redone after adding the runtime error checks,
these bullets must still be green. Indeed, the corresponding proofs have been
realized without the knowledge of the property in the assertion, so they cannot
rely on this unproved property.

When WP transmits a proof obligation to an automatic prover, it basically
transmits two types of properties : $G$, the goal, the property that we want
to prove, and $A_1$ ... $A_n$, the different assumptions we can have about
the state of the memory at the program point where we want to verify $G$.
However, it does not receive (in return) the properties that have been used
by the prover to validate $G$. So, if $A_3$ is an assumption, and if WP did
not succeed in getting a proof of $A_3$, it indicates that $G$ is true, but
only if we succeed in proving $A_3$.

The orange color indicates that no prover could determine if the property
is verified. There are two possibles reasons:

- the prover did not have enough information,
- the prover did not have enough time to compute the proof and encountered
  a timeout (which can be configured in the WP panel).

In the bottom panel, we can select the "WP Goals" tab, it shows the list of
proof obligations, and for each prover the result is symbolized by a logo
that indicates if the proof has been tried and if it succeeded, failed or
encountered a timeout (here we can see a try with Z3 where we had a timeout
on the proof of absence of RTE). Note that it may require to select
"All Results" in the squared field to see all proof obligations.

![Proof obligations panel of WP for `abs`](https://zestedesavoir.com:443/media/galleries/2584/d1c2dded-1e12-4cee-a575-7c990274f5c4.png)

In the first column, we have the name of the function the proof obligation
belongs to. The second column indicates the name of proof obligation. For
example here, our postcondition is named
"Post-condition 'positive_value,function_result'", we can notice that if
we select a property in this list, it is also highlighted in the source code.
Unnamed properties are automatically named by WP with the kind of wanted
property. In the third column, we see the memory model that is used for the
proof, we will not talk about it in this tutorial. Finally, the last columns
represent the different provers available through WP.

In these provers, the first element is Qed. It is not really a prover. In
fact, if we double-click on the property "absence of underflow"
(highlight in blue in the last screenshot), we can see this (if it is not
the case, make sure that the value "Raw obligation" is selected in the
blue squared field) :

![Proof obligation associated to the verification of absence of underflow in `abs`](https://zestedesavoir.com:443/media/galleries/2584/cf50837e-a119-40f9-8c93-c2b0bb03a142.png)

This is the proof obligation generated by WP about our property and our
program, we do need to understand everything here, but we can get the
general idea. It contains (in the "Assume" part) the assumptions that we
have specified and those that have been deduced by WP from the instructions
of the program. It also contains (in the "Prove" part) the property that
we want to verify.

What does WP do using these properties ? In fact, it transforms them into
a logic formula and then asks to different provers if it is possible to
satisfy this formula (to find for each variable, a value that can make the
formula true), and it determines if the property can be proved. But before
sending the formula to provers, WP uses a module called Qed, which is able
to perform different simplifications about it. Sometimes, as this is the
case for the other properties about `abs`, these simplifications are enough
to determine that the property is true, in such a case, WP do not need the
help of the automatic solvers.

When automatic solvers cannot ensure that our properties are verified, it
it sometimes hard to understand why. Indeed, provers are generally not able
to answer something other than "yes", "no" or "unknown", they are not able
to extract the reason of a "no" or an "unknown". There exists tools that
can explore a proof tree to extract this type of information, currently
Frama-C do not provide such a tool. Reading proof obligations can sometimes
be helpful, but it requires a bit of practice to be efficient. Finally, one
of the best way to understand the reason why a proof fails is to try to do
it interactively with Coq. However, it requires to be quite comfortable with
this language to not being lost facing the proof obligations generated by
WP, since these obligations need to encode some elements of the C semantics
that can make them quite hard to read.

If we go back to our view of proof obligations (see the red squared button
in the last screenshot), we can see that our hypotheses are not enough to
determine that the property "absence of underflow" is true (which is
indeed currently impossible), so we need to add some hypotheses to guarantee
that our function will well-behave: a call precondition.

# Preconditon

Preconditions are introduced using `requires` clauses. As we could do with
`ensures` clauses, we can compose logic expressions and specify multiple
preconditions:

```c
/*@
  requires 0 <= a < 100;
  requires b < a;
*/
void foo(int a, int b){
  
}
```

Preconditions are properties about the input (and eventually about global
variables) that we assume to be true when we analyze the function. We will
verify that they are indeed true only at program points where the function
is called.

In this small example, we can also notice a difference with C in the writing
of boolean expressions. If we want to specify that `a` is between 0 and 100,
we do not have to write `0 <= a && a < 100`, we can directly write
`0 <= a < 100` and Frama-C will perform necessary translations.

If we come back to our example about the absolute value, to avoid the
arithmetic underflow, it is sufficient to state that `val` must be strictly
greater than `INT_MIN` to guarantee that the underflow will never happen.
We then add it as a precondition of the function (notice that it is also
necessary to include the header where `INT_MIN` is defined):

```c
#include <limits.h>

/*@
  requires INT_MIN < val;

  ensures \result >= 0;
  ensures (val >= 0 ==> \result == val) && 
          (val < 0 ==> \result == -val);
*/
int abs(int val){
  if(val < 0) return -val;
  return val;
}
```

[[attention]]
| Reminder: The Frama-C GUI does not allow code source modification.

[[information]]
| For Frama-C NEON and older, the pre-processing of annotations is not
| activated by default. We have to start Frama-C with the option `-pp-annot`:
| ```bash
| $ frama-c-gui -pp-annot file.c
| ```

Once we have modified the source code with our precondition, we click on
"Reparse" and we can ask again to prove our program. This time, everything
is validated by WP, our implementation is proved:

![Proof of `abs` performed](https://zestedesavoir.com:443/media/galleries/2584/07785936-5148-406d-a432-5e88e4f25328.png)

We can also verify that a function that would call `abs` correctly
respects the required precondition:

```c
void foo(int a){
   int b = abs(42);
   int c = abs(-42);
   int d = abs(a);       // False : "a" can be INT_MIN
   int e = abs(INT_MIN); // False : the parameter must be strictly greater than INT_MIN
}
```

![Precondition checking when calling `abs`](https://zestedesavoir.com:443/media/galleries/2584/12a9ba65-5934-4d3e-bb52-d273d90fcf98.png)

We can modify this example by revering the last two instructions. If we
do this, we can see that the call `abs(a)` is validated by WP if it is
placed after the call `abs(INT_MIN)`! Why?

We must keep in mind that the idea of the deductive proof is to ensure that
if preconditions are verified, and if our computation terminates, then the
post-conditon is verified.

If we give a function that surely breaks the precondition, we can deduce that
the postconditon is false. Knowing this, we can prove absolutely everything
because this "false" becomes an assumption of every call that follows. Knowing
false, we can prove everything, because if we have a proof of false, then false
is true, as well as true is true. So everything is true.

Taking our modified program, we can convince ourselves of this fact by looking
at proof obligations generated by WP for the bad call and the subsequent call
that becomes verified:

![Generated proof obligation for the bad call](https://zestedesavoir.com:443/media/galleries/2584/997f0ae1-bd5a-45b5-a24f-56cbf934eb5f.png)

![Generated proof obligation for the call that follows](https://zestedesavoir.com:443/media/galleries/2584/f81582b8-e822-47c5-9600-ee34b0d04a21.png)

We can notice that for function calls, the GUI highlights the execution path
that leads to the call for which we want to verify the preconditon. Then, if
we have a closer look to the call `abs(INT_MIN)`, we can notice that,
simplifying, Qed deduced that we try to prove "False". Consequently, the next
call `abs(a)` receives in its assumptions the property "False". This is why
Qed can immediately deduce "True".

The second part of the question is then: why our first version of the calling
function (`abs(a)` and then `abs(INT_MIN)`) did not have the same behavior,
indicating a proof failure on the second call? The answer is simply that the
call `abs(a)` can, or not, produce an error, whereas `abs(INT_MIN)` necessarily
leads to an error. So, while `abs(INT_MIN)` necessarily gives us the knowledge
of "false", the call `abs(a)` does not, since it can succeed.

Produce a correct specification is then crucial. Typically, by stating false
precondition, we can have the possibility to create a proof of false:

```c
/*@
  requires a < 0 && a > 0;
  ensures  \false;
*/
void foo(int a){

}
```

If we ask WP to prove this function, it will accept it without a problem since
the assumption we give in precondition is necessarily false. However, we will
not be able to give an input that respects the precondition so we will be able
to detect this problem by carefully reading what we have specified.

Some notions we will see in this tutorial can expose us to the possibility to
introduce subtle incoherence. So, we must always be careful specifying a
program.

## Finding the right preconditions

Finding the right preconditions for a function is sometimes hard. The most
important idea is to determine these preconditions without taking in account
the content of the function (at least, in a first step), in order to avoid
building a specification that would contain the same bugs currently existing
in the source code, for example taking in account an erroneous conditional
structure. In fact, it is generally a good practice to work with someone else.
One specifies the function and the other implements it (even if they
previously agreed on a common textual specification).

Once these precondition has been stated, then we work on the specifications
that are due to the constraints of our language and our hardware. For example,
the absolute value do not really have a precondition, this is our hardware
that adds the condition we have given in precondition due to the two's
complement on which it relies.

# Some elements about the use of WP and Frama-C

In the two preceding sections, we have seen a lot of notions about the use
of the GUI to start proofs. In fact, we can ask WP to immediately prove
everything at Frama-C's startup with the option `-wp`:

```bash
$ frama-c-gui file.c -wp
```

Which will collect all properties to be proved inside `file.c`, generate all
proof obligations and try to discharge them.

About runtime-errors, it is generally advised to first verify the program
without generating RTE assertions, and then to generate them to terminate the
verification with WP. It allows WP to "focus" on the functional properties in
a first step without having in its knowledge base purely technical properties,
that are generally not useful for the proof of functional properties. Again,
it is possible to directly produce this behavior using the command line:

```bash
$ frama-c-gui file.c -wp -then -rte -wp
```

"Start Frama-C with WP, then create assertions to verify the absence of RTE
and start WP again".
