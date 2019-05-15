# Ensure program reliability

It is often difficult to ensure that our programs have only correct behaviors.
Moreover, it is already complex to establish good criteria that make us
confident enough to say that a program works correctly:

- beginners simply "try" to use their programs and considers that these
  programs work if they do not crash (which is not a really good indicator
  in C language),
- more advanced developers establish some test cases for which they know
  the expected result and compare the output they obtain,
- most companies establish complete test bases, that cover as much code
  as they can ; which are systematically executed on their code. Some of them
  apply test driven development,
- in critical domains, such as aerospace, railway or armament, every code
  needs to be certified using standardized processes with very strict
  criteria about coding rules and code covering by the test.

In all these ways to ensure that a program produces only what we expect it
to produce, a word appears to be common: *test*. We *try* different inputs
in order to isolate cases that are problematic. We provide inputs that we
*estimate to be representative* of the actual use of the program (note that
unexpected use case are often not considered whereas there are generally the
most dangerous ones) and we
verify that the results we get are correct. But we cannot test *everything*.
We cannot try *every* combination of *every* possible input of a program.
It is then quite hard to choose good tests.

The goal of program proof is to ensure that, for any input provided to a given
program, if it respects the specification, then the program will only
well-behave. However, since we cannot test everything, we will formally,
mathematically, establish a proof that our software can only exhibit specified
behaviors, and that runtime-errors are not part of these behaviors.

A very well-known quote from Dijkstra precisely express the difference between
test and proof :

> Program testing can be used to show the presence of bugs, but never to show 
> their absence!
Source: Dijkstra

## The developer's Holy Grail: the bug-free software

Every time we read news about attacks on computer systems, or viruses,
or bugs leading to crashes in well known apps, there is always the one same
comment "the bug-free/perfectly secure program does not exist". And, if
this sentence is quite true, it is a bit misunderstood.

Apart from the difference between safety and security (that we can very
vaguely define by the existence of a malicious entity), we do not really
define what we mean by "bug-free". Creating software always relies at least
on two steps: we establish a specification of what we expect from the
program and then we produce the source code of the program that must
respect this specification. Both of these steps can lead to the introduction
of errors.

In this tutorial, we will show how we can prove that an implementation verifies
a given specification. But what are the arguments of program proof, compared
to program testing? First, the proof is complete, it cannot forget some corner
case if the behavior is specified (program test cannot be complete,
being exhaustive would be far too costly). Then, the obligation to formally
specify with a logic formulation requires to exactly understand what we have
to prove about our program.

One could cynically say that program proof shows that "the implementation does
not contain bugs that do not exist in the specification". But, well, it is
already a big step compared to "the implementation does not contain too many
bugs that do not exist in the specification". Moreover, there also exist
approaches that allow to analyze specifications to find errors or under-specified
behaviors. For example, with model checking techniques, we can create an abstract
model from the specification and produce the set of states that can be reached
according to this model. By characterizing what is an error state, we can
determine if reachable states are error states.

# A bit of context

Formal methods, as we name them, allow in computer science to rigorously,
mathematically, reason about programs. There exist a lot of formal methods that
can take place at different levels from program design to implementation,
analysis and validation, and for all systems that allow to manipulate information.

Here, we will focus on a method that allows to formally verify that our programs
have only correct behaviors. We will use tools that are able to analyze a source
code and to determine whether a program correctly implements what we want to
express. The analyzer we will use provides a static analysis, that we can oppose
to dynamic analysis.

In static analysis, the analyzed program is not executed. We reason on a
mathematical model of the states it can reach during its execution. On the
opposite, dynamic analyses such as program testing, require to execute the
analyzed source code. Note that there exist formal dynamic analysis methods, for
example automatic test generation, or code monitoring techniques that allow to
instrument a source code to verify some properties about it during execution
(correct memory use, for example).

Talking about static analyses, the model we use can be more or less abstract
depending on the techniques, it is always an approximation of possible states of
the program. The more the approximation is precise, the more the model is
concrete, the more the approximation is vague, the more it is abstract.

To illustrate the difference between concrete and abstract model, we can have
a look to the model of a simple chronometer. A very abstract model of a chronometer
could be the following one:

![A very abstract model of a chronometer](https://zestedesavoir.com:443/media/galleries/2584/be01ae1b-a9fd-4147-aa1f-98542f030a4d.png)

We have a model of the behavior of our chronometer with the different states
it can reach according to the different actions we can perform. However, we do
not have modeled how these states are depicted inside the program (is this a
C enumeration? a particular program point in the source code?), nor how is
modeled the time computation (a single variable? multiple ones?). It would
then be difficult to specify properties about our program. We could add some
information:

- State stopped at 0 : time = 0s
- State running : time > 0s
- State stopped : time > 0s

Which gives us a more concrete model but that is still not precise enough to
ask interesting questions like: "is it possible to be in the state stopped and
that time is still updated?", as we do not model how the time measurement is
updated by the chronometer.

On the opposite, with the source code of the program, we have a concrete model
of the chronometer. The source code expresses the behavior of the chronometer
since it will allow us to produce the executable. But this is still not the
more concrete model! For example, the executable in machine code format, that
we obtain after compilation, is far more concrete than our program.

The more a model is concrete, the more it precisely describes the behavior of
our program. The source code more precisely describes the behavior than our
diagram, but it is less precise than the machine code. However, the more the
model is precise, the more it is difficult to have a global view of the defined
behavior. Our diagram is understandable in the blink of an eye, the source code
requires more time, and for the executable ... Every single person that has
already opened an executable with a text editor by error knows that it is not
really pleasant to read[^binary].

When we create an abstraction of a system, we approximate it, in order to
limit the knowledge we have about it and ease our reasoning.
A constraint we must respect, if we want our analysis to be correct, is to
never under-approximate behaviors: we would risk to remove a behavior that
contains an error. However, when we over-approximate it, we can add behaviors
that cannot happen, and if we add too many of them, we could not be able to
prove our program is correct, since some of them could be faulty behaviors.

In our case, the model is quite concrete. Every type of instruction, of control
structure, is associated to a precise semantics, a model of its behavior in a
pure logic, mathematical, world. The logic we use here is a variant of the
Hoare logic, adapted to the C language and all its complex subtleties (which
makes this model concrete).

[^binary]: There also exists formal methods which are interested in
understanding how executable machine code work, for example in order to
understand what malwares do or to detect security breaches introduced during
compilation.

# Hoare triples

Hoare logic is a program formalization method proposed by Tony Hoare in 1969
in a paper entitled *An Axiomatic Basis for Computer Programming*. This method
defines:

- axioms, that are properties we admit, such as "the skip action does not
  change the program state",
- rules to reason about the different allowed combinations of actions, for
  example "the skip action followed by the action A" is equivalent to "the
  action A".

The behavior of the program is defined by what we call "Hoare triples":

-> $\{P\} C \{Q\}$ <-

Where $P$ and $Q$ are predicates, logic formulas that express properties about
the memory at particular program points. $C$ is a list of instructions that
defines the program. This syntax expresses the following idea: "if we are in 
a state where $P$ is verified, after executing $C$ and if $C$ terminates, then
$Q$ is verified for the new state of the execution". Put in another way, $P$
is a sufficient precondition to ensure that $C$ will bring us to the
postcondition $Q$. For example, the Hoare triples that corresponds to the
skip action is the following one:

-> $\{P\}$ **skip** $\{P\}$ <-

When we do nothing, the postcondition is the precondition.

Along this tutorial, we will present the semantics of different program
constructs (conditional blocks, loops, etc) using Hoare logic. So, we will
not enter into details now since we will work on it later. It is not
necessary to memorize these notions nor to understand all the theoretical
background, but it is still useful to have some ideas about the way our
tool works.

All of this gives us the basics that allow us to say "here is what this
action does" but it does not give us anything to mechanize a proof. The tool
we will use rely on a technique called weakest precondition calculus.

# Weakest precondition calculus

The weakest precondition calculus is a form of predicate transform semantics
proposed by Dijkstra in 1975 in *Guarded commands, non-determinacy and formal
derivation of programs*.

This sentence can appear complex but the actual meaning is in fact quite
simple. We have seen before that Hoare logic gives us rules that explain the
behavior of the different actions of a program, but it does not say how to
apply these rules to establish a complete proof of the program.

Dijkstra reformulate the Hoare logic by explaining, in the triple 
$\{P\}C\{Q\}$, how the instruction, or the block of instructions, $C$
transforms the predicate $P$ in $Q$. This kind of reasoning is called
*forward-reasoning*. We calculate from the precondition and from one or
multiple instructions, the strongest postcondition we can reach.
Informally, considering what we have in input, we calculate what we will
get in output. If the postcondition we want is as strong or weaker, then
we prove that there are no unwanted behaviors.

For example:

```c
int a = 2;
a = 4;
//calculated postcondition : a == 4
//wanted postcondition     : 0 <= a <= 30
```

Ok, 4 is an allowed value for `a`.

The form of predicate transformer semantics which we are interested in
works the opposite way, we speak about *backward-reasoning*. From the wanted
postcondition and the instructions we are reasoning about, we find the
weakest precondition that ensures this behavior. If our actual precondition is
at least as strong, that is to say, if it implies the computed precondition,
then our program is correct.

For example, if we have the instruction:

$\{P\}$ $x$ $:=$ a $\{x = 42\}$

What is the weakest precondition to validate the postcondition $\{x = 42\}$ ?
The rule will define that $P$ is $\{$a$=42\}$.

For now, let us forget about it, we will come back to these notions as we
use them in this tutorial to understand how our tools work. So now, we can
have a look at these tools.
