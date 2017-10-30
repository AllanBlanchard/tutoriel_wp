# Assignment

Assignment is the most basic operation one can have in language (leaving aside
the "do nothing" operation that is not particularly interesting).
The weakest precondition calculus associates the following computation to an
assignment operation;

-> $wp(x = E , Post) := Post[x \leftarrow E]$ <-

Here the notation $P[x \leftarrow E]$ means "the property $P$ where $x$ is
replaced by $E$". In our case this corresponds to "the postcondition $Post$
where $x$ is replaced by $E$".
The idea is that the postcondition of an assignment of $E$ to $x$ can
only be true if replacing all occurrences of $x$ in the formula by $E$ is true.
For example:

```c
// { P }
x = 43 * c ;
// { x = 258 }
```

-> $P = wp(x = 43*c , \{x = 258\}) = \{43*c = 258\}$ <-

The function $wp$ allows us to compute as weakest precondition of the
the assignment the formula $\{43*c = 258\}$, thus obtaining the following
Hoare triple:

```c
// { 43*c = 258 }
x = 43 * c ;
// { x = 258 }
```

In order to compute the precondition of the assignment we have replaced each
occurrence of $x$ in the postcondition by the assigned value $E = 43*c$.
If our program were of the form:

```c
int c = 6 ;
// { 43*c = 258 }
x = 43 * c ;
// { x = 258 }
```

we could submit the formula " $43*6 = 258$ " to our automatic prover in order
to determine whether it is really valid. The answer would of course be "yes"
because the property is easy to verify. If we had, however, given the value
7 to the variable `c` the prover's reply would be "no" since the formula
$43*7 = 258$ is not true.

Taking into account the weakest precondition calculus, we can now write the
inference rule for the Hoare triple of an assignment as

-> $\dfrac{}{\{Q[x \leftarrow E] \}\quad x = E \quad\{ Q \}}$ <-

We note that there is no precondition to verify. Does this mean that the triple
is necessarily true? Yes. However, it does not mean that the precondition is
respected by the program to which the assignment belongs or that the
precondition is at all possible. Here the automatic provers come into play.

For example, we can ask Frama-C to verify the following line

```c
int a = 42;
//@ assert a == 42;
```

which is, of course, directly proven by Qed, since it is a simple applications
of the assignment rule.

[[information]]
| We remark that according to the C standard, an assignment is in fact an
| expression. This allows us, for example, to write `if( (a = foo()) == 42)`.
| In Frama-C, an assignment will always be treated as a statement. Indeed,
| if an assignment occurs within a larger expression, then the Frama-C
| kernel, while building the abstract syntax tree, systematically
| performs a *normalization step* that produces a separate assignment
| statement.


# Composition of statements

For a statement to be valid, its precondition must allow us by means of
executing the said statement to reach the desired postcondition.
Now we would like to execute several statements one after another.
Here the idea is that the postcondition of the first statement is compatible
with the required precondition of the second statement and so on for the third
statement.

The inference rule that corresponds to this idea utilizes the following
Hoare triples:


-> $\dfrac{\{P\}\quad S1 \quad \{R\} \ \ \ \{R\}\quad S2 \quad \{Q\}}{\{P\}\quad S1 ;\ S2 \quad \{Q\}}$ <-

In order to verify the composed statement $S1;\ S2$ we rely on an
intermediate property $R$ that is at the same time the postcondition of $S1$
and the precondition of $S2$. (Please note that $S1$ and $S2$ are not necessarily
simple statements; they themselves can be composed statements.)
The problem is, however, that nothing indicates us how to determine the
properties $P$ and $R$.

The weakest-precondition calculus now says us that the intermediate property $R$
can be computed as the weakest precondition of the second statement. The
property $P$, on the other hand, then is computed as the weakest precondition
of the first statement. In other words, the weakest precondition of the composed
statement $S1; S2$ is determined as follows:

-> $wp(S1;\ S2 , Post) := wp(S1, wp(S2, Post) )$ <-

The WP plugin of Frama-C performs all these computations for us.
Thus, we do not have to write the intermediate properties as ACSL assertions
between the lines of codes.

```c
int main(){
  int a = 42;
  int b = 37;

  int c = a+b; // i:1
  a -= c;      // i:2
  b += a;      // i:3

  //@assert b == 0 && c == 79;
}
```

## Proof tree

When we have more than two statements, we can consider the last statement as
second statement of our rule and all the preceding ones as first statement.
This way we traverse step by step backwards the statements in our reasoning.
With the previous program this looks like:

+-------------------------------------------+------------------------------------------------+---------------------------------------------+
| -> $\{P\}\quad i_1 ; \quad \{Q_{-2}\}$ <- | -> $\{Q_{-2}\}\quad i_2 ; \quad \{Q_{-1}\}$ <- |                                             |
+-------------------------------------------+------------------------------------------------+---------------------------------------------+
| -> $\{P\}\quad i_1 ; \quad i_2 ; \quad \{Q_{-1}\}$ <-                                      | -> $\{Q_{-1}\} \quad i_3 ; \quad \{Q\}$ <-  |
+--------------------------------------------------------------------------------------------+---------------------------------------------+
| -> $\{P\}\quad i_1 ; \quad i_2 ; \quad i_3 ; \quad \{ Q \}$ <-                                                                           |
+------------------------------------------------------------------------------------------------------------------------------------------+

The weakest-precondition calculus allows us to construct the property $Q_{-1}$
starting from the property $Q$ and statement $i_3$ which in turn enables us
to derive the property $Q_{-2}$ from the property $Q_{-1}$ and statement $i_2$.
Finally, $P$ can be determined from $Q_{-2}$ and $i_1$.

Now that we can verify programs that consists of several statements it
is time to add some structure to them.

# Conditional rule

For a conditional statement to be true, one must be able to reach the
postcondition through both branches.
Of course, for both branches the same precondition (of the conditional
statement) must hold. In addition we have that in the if-branch
the condition is true while in the else-branch it is false.

We therefore have, as in the case of composed statements, two facts to verify
(in order to avoid confusion we are using here the syntax
$if\ B\ then\ S1\ else\ S2$):

-> $\dfrac{\{P \wedge B\}\quad S1\quad \{Q\} \quad \quad \{P \wedge \neg B\}\quad S2\quad \{Q\}}{\{P\}\quad if\quad B\quad then\quad S1\quad else\quad S2 \quad \{Q\}}$ <-

Our two premises are therefore that we can both in the if-branch and the
else-branch reach the postcondition from the precondition.

The result of the weakest-precondition calculus for a conditional statement
reads as follows:

-> $wp(if\ B\ then\ S1\ else\ S2 , Post) := (B \Rightarrow wp(S1, Post)) \wedge (\neg B \Rightarrow wp(S2, Post))$ <-

This means that the condition $B$ has to imply the weakest precondition of $S1$
in order to safely arrive at the postcondition.
Analogously, the negation of $B$ must imply the weakest precondition of $S2$.

## Empty else-branch

Following this definition we obtain for case of an empty else-branch the
following rule by simply replacing the statement $S2$ by the empty statement
`skip`.


-> $\dfrac{\{P \wedge B\}\quad S1\quad \{Q\} \quad \quad \{P \wedge \neg B\}\quad skip\quad \{Q\}}{\{P\}\quad if\quad B\quad then\quad S1\quad else\quad skip \quad \{Q\}}$ <-

The triple for `else` is:

-> $\{P \wedge \neg B\}\quad skip\quad \{Q\}$ <-

which means that we need to ensure:

-> $P \wedge \neg B \Rightarrow Q$ <-

In short, if the condition $B$ of `if` is false, this means that the
postcondition of the complete conditional statement is already established
before entering the else-branch (since it does not do anything).

As an example, we consider the following code snippet where we reset a variable
$c$ to a default value in case it had not been properly initialized by the user.

```c
int c;

// ... some code ...

if(c < 0 || c > 15){
  c = 0;
}
//@ assert 0 <= c <= 15;
```

Let

$wp(if \neg (c \in [0;15])\ then\ c := 0, \{c \in [0;15]\})$

$:= (\neg (c \in [0;15])\Rightarrow wp(c := 0, \{c \in [0;15]\})) \wedge (c \in [0;15]\Rightarrow wp(skip, \{c \in [0;15]\}))$

$= (\neg (c \in [0;15]) \Rightarrow 0 \in [0;15]) \wedge (c \in [0;15] \Rightarrow c \in [0;15])$

$= (\neg (c \in [0;15]) \Rightarrow true) \wedge true$

The property can be verified: independent of the evaluation of
$\neg (c \in [0;15])$, the implication will hold.
