Loops need a particular treatment in deductive verification of programs.
These are the only control structures that will require important work
from us. We cannot avoid this because without loops, it is difficult to
write and prove interesting programs.

Before we look at the way we specify loop, we can answer to a rightful
question: why are loops so complex?

# Induction and invariant

The nature of loops makes their analysis complex. When we perform our backward
reasoning, we need a rule to determine the precondition from a given sequence
of instructions and a post-condition. Here, the problem is that we cannot *a
priori* deduce how many times a loop will iterate, and consequently, we cannot
know how many times variables will be modified.

We will then proceed using an inductive reasoning. We have to find a property
that is true before we start to execute the loop and that, if it is true at the
beginning of an iteration, remains true at the end (and that is consequently
true at the beginning of the next iteration).

This type of property is called a loop invariant. A loop invariant is a property
that must be true before and after each loop iteration. For example with the
following loop:

```c
for(int i = 0 ; i < 10 ; ++i){ /* */ }
```

The property $0 <= i <= 10$ is a loop invariant. The property $-42 <= i <= 42$
is also an invariant (even if it is far less precise). The property
$0 < i <= 10$ is not an invariant because it is not true at the beginning of
the execution of the loop. The property $0 <= i < 10$ **is not a loop
invariant**, it is not true at the end of the last iteration that sets the value
of `i` to $10$.

To verify an invariant $I$, WP will then produce the following "reasoning":

- verify that $I$ is true at the beginning of the loop (establishment)
- verify that if $I$ is true before an iteration, then $I$ is true after (preservation).

## [Formal] Inference rule

Let us note the invariant $I$, the inference rule corresponding to loops is
defined as follows:

-> $\dfrac{\{I \wedge B \}\ c\ \{I\}}{\{I\}\ while(B)\{c\}\ \{I \wedge \neg B\}}$ <-

And the weakest precondition calculus is the following:

-> $wp(while (B) \{ c \}, Post) := I \wedge ((B \wedge I) \Rightarrow wp(c, I)) \wedge ((\neg B \wedge I) \Rightarrow Post)$ <-

Let us detail this formula:

- (1) the first $I$ corresponds to the establishment of the invariant, in
  layman's terms, this is the "precondition" of the loop,
- the second part of the conjunction ($(B \wedge I) \Rightarrow wp(c, I)$)
  corresponds to the verification of the operation performed by the body of
  the loop:
    - the precondition that we know of the loop body (let us note $KWP$,
      "Known WP") is ($KWP = B \wedge I$). That is the fact we have entered the
      loop ($B$ is true), and that the invariant is verified at this moment
      ($I$, is true before we start the loop by (1), and we want to verify that
      it will be true at the end of the body of the loop in (2)),
    - (2) it remains to verify that $KWP$ implies the actual precondition\* of
      the body of the loop ($KWP \Rightarrow wp(c, Post)$). What we want at the
      end of the loop is the preservation of the invariant $I$ ($B$ is maybe
      not true anymore however), formally $KWP \Rightarrow wp(c, I)$, that is to
      say $(B \wedge I) \Rightarrow wp(c, I)$,
    - \* it corresponds to the application of the consequence rule previously
      explained.
- finally, the last part ($(\neg B \wedge I) \Rightarrow Post$) expresses the
  fact that when the loop ends($\neg B$), and the invariant $I$ has been
  maintained, it must imply that the wanted postcondition of the loop is valid.

In this computation, we can notice that the $wp$ function does not indicate any
way to obtain the invariant $I$. We have to specify ourselves this property
about our loops.

## Back to the WP plugin

There exist tools that can infer invariant properties (provided that these
properties are simple, automatic tools remain limited). This is not the case for
WP. We will have to manually annotate our programs to specify the invariant of
each loop. To find and write invariants for our loops will always be the hardest
part of our work when we want to prove programs.

Indeed, when there are no loops, the weakest precondition calculus function
can automatically provide the verifiable properties of our programs. This is not
the case for loop invariant properties for which we do not have computation
procedures. We have to find and express them correctly, and depending on the
algorithm, they can be quite subtle and complex.

In order to specify a loop invariant, we add the following annotations before
the loop:

```c
int main(){
  int i = 0;
  
  /*@
    loop invariant 0 <= i <= 30;
  */
  while(i < 30){
    ++i;
  }
  //@assert i == 30;
}
```

[[attention]]
| **REMINDER** : The invariant is: i **<=** 30 !

Why? Because along the loop, `i` will be comprised between 0 and **included**
30. 30 is indeed the value that allows us to leave the loop. Moreover, one of
the properties required by the weakest precondition calculus is that when the
loop condition is invalidated, by knowing the invariant, we can prove the
postcondition (Formally $(\neg B \wedge I) \Rightarrow Post$).

The postcondition of our loop is `i == 30` and must be implied by 
$\neg$ ```i < 30``` $\wedge$ ```0 <= i <= 30```. Here, it is true since:
```i >= 30 && 0 <= i <= 30 ==> i == 30```. On the opposite, if we exclude the
equality to 30, the postcondition would be unreachable.

Again, we can have a look at the list of proof obligations in "WP Goals":

![Proof obligations generated to verify our loop](https://zestedesavoir.com:443/media/galleries/2584/3e2cfa83-cbf8-48fd-b716-9baf51a91ed3.png)

We note that WP produces two different proof obligations: the establishment of
the invariant and its preservation. WP produces exactly the reasoning we
previously described to prove the assertion. In recent versions of Frama-C, Qed
has become particularly aggressive and powerful, and the generated proof
obligation does not show these details (showing directly "True"). Using the
option `-wp-no-simpl` at start, we can however see these details:

![Proof of the assertion, knowing the invariant and the invalidation of the loop condition](https://zestedesavoir.com:443/media/galleries/2584/e74c959b-b551-437e-827f-7a01732101b5.png)

But is our specification precise enough?

```c
int main(){
  int i = 0;
  int h = 42;
  
  /*@
    loop invariant 0 <= i <= 30;
  */
  while(i < 30){
    ++i;
  }
  //@assert i == 30;
  //@assert h == 42;
}
```

And the result is:

![Side-effects, again](https://zestedesavoir.com:443/media/galleries/2584/6243b4fe-2c54-4762-babf-ba1229c4b665.png)

It seems not.

# The assigns clause ... for loops

In fact, considering loops, WP **only** reasons about what is provided by
the user to perform its reasoning. And here, the invariant does not specify
anything about the way the value of `h` is modified (or not). We could specify
the invariant of all program variables, but it would be a lot of work. ACSL
simply allows to add `assigns` annotations for loops. Any other variable is
considered to keep its old value. For example:

```c
int main(){
  int i = 0;
  int h = 42;
  
  /*@
    loop invariant 0 <= i <= 30;
    loop assigns i;
  */
  while(i < 30){
    ++i;
  }
  //@assert i == 30;
  //@assert h == 42;
}
```

This time, we can establish the proof that the loop correctly behaves. However,
we cannot prove that it terminates. The loop invariant is not enough to perform
such a proof. For example, in our program, we could modify the loop, removing
the loop body:

```c
/*@
  loop invariant 0 <= i <= 30;
  loop assigns i;
*/
while(i < 30){
   
}
```

The invariant is still verified, but we cannot prove that the loop ends:
it is infinite.

# Partial correctness and total correctness - Loop variant

In deductive verification, we find two types of correctness, the partial
correctness and the total correctness. In the first case, the formulation of
the correctness property  is "if the precondition is valid, and **if** the
computation terminates, then the postcondition is valid". In the second case,
"if the precondition is valid, **then** the computation terminates and the
postcondition is valid". By default, WP considers only partial correctness:

```c
void foo(){
  while(1){}
  //assert \false;
}
```

If we try to verify this code activating the verification of absence of RTE,
we get this result:

![Proof of false by non termination](https://zestedesavoir.com:443/media/galleries/2584/dba607cc-eb6e-4f8a-83b5-89f353981615.png)

The assertion "False" is proved! For a very simple reason: since the condition
of the loop is "True" and no instruction of the loop body allows to leave the
loop, it will not terminate. As we are proving the code with partial
correctness, and as the execution does not terminate, we can prove anything
about the code that follows the non terminating part of the code. However, if
the termination is not trivially provable, the assertion will probably not be
proved.

[[information]]
| Note that a (provably) unreachable assertion is always proved to be true:
[
| ![We "jump" after an assertion using goto](https://zestedesavoir.com:443/media/galleries/2584/eafe5462-e97f-4b9b-8581-c8d9b4ecca5c.png)
|
| And this is also the case when we trivially know that an instruction
| produces a runtime error (for example dereferencing `NULL`), or inserting
| "False" in post-condition as we have already seen with `abs` and the
| parameter `INT_MIN`.

In order to prove the termination of a loop, we use the notion of loop variant.
The loop variant is not a property but a value. It is an expression that involves
the element modified by the loop and that provides an upper bound to the number
of iterations that have to be executed by the loop at each iteration. Thus, it is
an expression greater or equal to 0, and that strictly decreases at each loop
iteration (this will also be verified by induction by WP).

If we take our previous example, we add the loop variant with this syntax:


```c
int main(){
  int i = 0;
  int h = 42;
  
  /*@
    loop invariant 0 <= i <= 30;
    loop assigns i;
    loop variant 30 - i;
  */
  while(i < 30){
    ++i;
  }
  //@assert i == 30;
  //@assert h == 42;
}
```

Again, we can have a look at the generated proof obligations:

![Our loop entirely specified and proved](https://zestedesavoir.com:443/media/galleries/2584/077e05ac-1841-4a19-9309-000807fc35bf.png)

The loop variant generates two proof obligations: verify that the value
specified in the variant is positive, and prove that it strictly decreases during
the execution of the loop. And if we delete the line of code that increments `i`,
WP cannot prove anymore that `30 - i` strictly decreases.

We can also note that being able to give a loop invariant does not necessarily
induce that we can give the exact number of remaining iterations of the loop, as
we do not always have a so precise knowledge of the behavior of the program. We
can for example build an example like this one:

```c
#include <stddef.h>

/*@
  ensures min <= \result <= max;
*/
size_t random_between(size_t min, size_t max);

void undetermined_loop(size_t bound){
  /*@
    loop invariant 0 <= i <= bound ;
    loop assigns i;
    loop variant i;
   */
  for(size_t i = bound; i > 0; ){
    i -= random_between(1, i);
  }
}
```

Here, at each iteration, we decrease the value of the variable `i` by a value
comprised between 1 and `i`. Thus, we can ensure that the value of `i` is
positive and strictly decreases during each loop iteration, but we cannot say
how many loop iteration will be executed.

The loop variant is then only an upper bound on the number of iteration, not
an expression of their exact number.

# Create a link between post-condition and invariant

Let us consider the following specified program. Our goal is to prove that
this function returns the old value of `a` plus 10.

```c
/*@
    ensures \result == \old(a) + 10;
*/
int add_10(int a){
    /*@
        loop invariant 0 <= i <= 10;
        loop assigns i, a;
        loop variant 10 - i;
    */
    for (int i = 0; i < 10; ++i)
        ++a;

    return a;
}
```

The weakest precondition calculus does not allow to deduce information that is
not part of the loop invariant. In a code like:

```c
/*@
    ensures \result == \old(a) + 10;
*/
int add_10(int a){
    ++a;
    ++a;
    ++a;
    //...
    return a;
}
```

By reading the instructions backward from the postcondition, we always keep all
knowledge about `a`. On the opposite, as we previously mentioned, outside the
loop, WP only considers the information provided by the invariant. Consequently,
our "add_10" function cannot be proved: the invariant does not say anything
about `a`. To create a link between the postcondition and the invariant, we have
to add this knowledge. For example:

```c
/*@
    ensures \result == \old(a) + 10;
*/
int add_10(int a){
    /*@
        loop invariant 0 <= i <= 10;
        loop invariant a = \old(a) + i; //< ADDED
        loop assigns i, a;
        loop variant 10 - i;
    */
    for (int i = 0; i < 10; ++i)
        ++a;

    return a;
}
```

[[information]]
| This need can appear as a very strong constraint. This is not really the case.
| There exists strongly automated analysis that can compute loop invariant
| properties. For example, without a specification, an abstract interpretation
| would easily compute `0 <= i <= 10` and `old(a) <= a <= \old(a)+10`. However,
| it is often more difficult to compute the relations that exist between the
| different variables of a program, for example the equality expressed by the
| invariant we have added.
