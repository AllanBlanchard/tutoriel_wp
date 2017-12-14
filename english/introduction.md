[[information]]
| In this tutorial, some examples and some elements of organization are similar
| to the ones used in the [TAP 2013 tutorial](http://www.spacios.eu/TAP2013/keynotes.html)
| by Nikolai Kosmatov, Virgile Prevosto and Julien Signoles of the CEA LIST,
| since it is quite didactic. It also contains examples taken from 
| *[ACSL By Example](http://www.fokus.fraunhofer.de/download/acsl_by_example)* 
| by Jochen Burghardt, Jens Gerlach, Kerstin Hartig, Hans Pohl and Juan Soto 
| from the Fraunhofer. The remaining ideas come from my personal experience with
| Frama-C and WP.
|
| The only pre-requisite to this tutorial is to have a basic knowledge of the
| C language, and at least to be familiar with the notion of pointer.

Despite its old age, C is still a widely used programming language. Indeed,
no other language can pretend to be available on so many different (hardware
and software) platforms, its low-level orientation and the amount of time
invested in the optimization of its compilers allows to generate very light
and efficient machine code (if the code allows it of course), and that there
are a lot of experts in C language, which is an important knowledge base.

Furthermore, a lot of systems rely on a huge amount of code historically
written in C, that needs to be maintained and sometimes fixed, as it would
be far too costly to rewrite these systems.

But anyone who has already developed with C also know that it is very hard
to perfectly master this language. There are numerous reasons, but ambiguities
in the ISO C, and the fact that it is extremely permissive, especially about
memory management, make the development of robust C program very hard, even
for an experienced programmer.

However, the C language is often chosen for critical systems (avionics,
railway, armament, ...) where it is appreciated for its good performances,
its technological maturity and the predictability of its compilation.

In such cases, the needs in term of code covering by tests become important.
The question "is our software tested enough?" becomes a question to which
it is very hard to answer. Program proof can help us. Rather than test all
possible and (un)imaginable inputs to the program, we will *mathematically*
prove that there cannot be any problem at runtime.

The goal of this tutorial is to use Frama-C, a tool developed at the CEA
LIST, and WP, its deductive proof plugin, to learn the basics about C program
proof. More than the use of the tool itself, the goal of this tutorial is
to convince that it is more and more possible to write programs without any
programming error, but also to sensitize to simple notions that allows to
better understand and write programs.

[[information]]
| Many thanks to the different beta-testers for their constructive feedback:
| 
| - [Taurre](https://zestedesavoir.com/membres/voir/Taurre/) (the example in
| the section III - 3 - 4 has been shamefully ripped off from one of his
| posts)
| - [barockobamo](https://zestedesavoir.com/membres/voir/barockobamo/)
| - [Vayel](https://zestedesavoir.com/membres/voir/Vayel/)
|
| I thank ZesteDeSavoir validators who helped me improve again the quality of
| this tutorial:
|
| - [Taurre](https://zestedesavoir.com/membres/voir/Taurre/) (again)
| - [Saroupille](https://zestedesavoir.com/membres/voir/Saroupille/)
|
| Finally, many thanks to Jens Gerlach for his help during the translation of
| this tutorial from French to English.
