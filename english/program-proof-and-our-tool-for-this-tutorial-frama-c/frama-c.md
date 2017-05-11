->![](http://frama-c.com/modern/framac.gif)<-

# Frama-C ? WP ?

Frama-C (FRAmework for Modular Analysis of C code) is a platform dedicated
to the analysis of C programs created by the CEA List and Inria. It is based
on a modular architectures allowing to use different (collaborating or not)
plugins. The default plugins comprises different static analyses (that do not
executed source code), dynamic analyses (that requires code execution), or
combining both.

Frama-C provides a specification language called ACSL ("Axel") for ANSI C
Specification Language and that allows us to express the properties we want
to verify adout our programs. These properties will be written using code
annotations in comments sections. If one have already used Doxygen, it is
quite similar, except that we write logic formulas and not text. During this
tutorial, we will extensively write ASCL code, so let us just skip this for
now.

The analysis we will use is provided by the WP plugin (for Weakest Precondition),
it implements the technique we presented earlier : from ACSL annotations and
the source code, the plugin generates what we call proof goals, that are logic
formulas that are then verified to be satisfiable or not. This verification can
be performed manually or automatically, here we use automatic tools.

We will use a SMT solver 
([statisfiability modulo theory](https://en.wikipedia.org/wiki/Satisfiability_modulo_theories),
we will not detailed how it works). This solver is  
[Alt-Ergo](http://alt-ergo.lri.fr/), initially developed by the
Laboratoire de Recherche en Informatique d'Orsay, and is today maintained and
updated by OCamlPro.

# Installation

Frama-C is developed under Linux and OSX. It is then better supported under
these two. It is still possible to install it on Windows and its use would be
equivalent to the one we could have on Linux but:

[[attention]]
| - the tutorial presents the use of Frama-C on Linux (or OSX) and the author
|   did not experiment the differences that could exists with Windows,
| - the "Bonus" section of this part could not be accessible under Windows.

## Linux

### Using package managers

Under Debian, Ubuntu and Fedora, there exist packages for Frama-C. In such a
case, it is enough to type a command like :

```bash
apt-get/yum install frama-c
```

However, these repositories are not necessarily up to date with the last
version of Frama-C. That is not a big problem since there is not new versions
of Frama-C every day, but it still important to know it.

Go to the section "Verify installation" to perform some tests about your
installation.

### Via opam

A second option is to use Opam, a package manager for Ocaml libraries and
applications.

First of all, Opam must be installed (see its documentation). Then, some
packages from your Linux distribution must be installed  before installing
Frama-C:

- lib gtk2 dev
- lib gtksourceview2 dev
- lib gnomecanvas2 dev
- (recommended) lib zarith dev

Once it is done, we can install Frama-C and Alt-Ergo.

```bash
opam install frama-c
opam install alt-ergo
```

Go to the section "Verify installation" to perform some tests about your
installation.

### Via "manual" compilation

The package we have listed in the Opam section are required (of course, Opam
itself is not). It requires a recent version of Ocaml and its compiler
(including compiler to native code).

After having extracted the folder available here :
[http://frama-c.com/download.html](http://frama-c.com/download.html) (Source distribution). 
Navigate to the folder and then execute the command line:
```bash
./configure && make && sudo make install
```

Go to the section "Verify installation" to perform some tests about your
installation.

## OSX

On OSX, the use of Homebrew and Opam is recommended to install Frama-C.
The author do not use OSX, so here is an awful copy and paste of the
installation guide of Frama-C for OSX.

General Mac OS tools for OCaml:

```bash
> xcode-select --install
> open http://brew.sh
> brew install autoconf opam
```
Graphical User Interface:
```bash
> brew install gtk+ --with-jasper
> brew install gtksourceview libgnomecanvas graphviz
> opam install lablgtk ocamlgraph 
```

Recommended for Frama-C:
```bash
> brew install gmp
> opam install zarith
```

Necessary for Frama-C/WP:
```bash
> opam install alt-ergo
> opam install frama-c
```

Also recommended for Frama-C/WP:
```bash
opam install altgr-ergo coq coqide why3
```

Go to the section "Verify installation" to perform some tests about your
installation.

## Windows

Currently, the installation of Frama-C for Windows requires Cygwin and an
experimental version of Opam for Cygwin. So we need to install both as well
as the MinGW Ocaml compiler.

Installation instructions can be found there :

[Frama-C - Windows](https://bts.frama-c.com/dokuwiki/doku.php?id=mantis:frama-c:compiling_from_source)

Frama-C is then started using Cygwin.

Go to the section "Verify installation" to perform some tests about your
installation.

# Verify installation

In order to verify that the installation has been correctly performed, we
will use this simple code in a file `main.c`:

```c
/*@
  requires \valid(a) && \valid(b);
  assigns *a, *b;
  ensures *a == \old(*b);
  ensures *b == \old(*a);
*/
void swap(int* a, int* b){
  int tmp = *a;
  *a = *b;
  *b = tmp;
}

int main(){
  int a = 42;
  int b = 37;

  swap(&a, &b);

  //@ assert a == 37 && b == 42;

  return 0;
}
```

Then, from a terminal, in the folder where the file has been created,
we start Frama-C with the following command line:

```bash
frama-c-gui -wp -rte main.c
```

This window should open:

![Verify installation 1](https://zestedesavoir.com:443/media/galleries/2584/c5a510d2-0252-4c40-a621-071a3130a641.png)

Clicking `main.c` in the left side panel to select it, we can see its
content (slightly) modified, and some green bullets on different lines
like this:

![Verify installation 2](https://zestedesavoir.com:443/media/galleries/2584/8e6fc038-29e5-479f-affd-9040454dc3aa.png)

[[attention]]
| The graphical user interface of Frama-C do not allow source code edition

[[information]]
| For color blinds, it is possible to start Frama-C with another theme where
| color bullets are replaced:
| ```bash
| $ frama-c-gui -gui-theme colorblind
| ```

# (Bonus) Some more provers

This part is optional, nothing in this section should be particularly useful
*in the tutorial*. However, when we start to be interested in proving more
complex programs, it is often possible to reach the limits of Alt-Ergo, which
is basically available, and to need some other provers.

## Coq

Coq, which is developed by Inria, is proof assistant. Basically, we write
the proofs ourselves in a dedicated language and the platform verify (using
typing) that the proof is actually a valid proof.

Why would we need such a tool ? Sometimes, the properties we want to prove
can be too complex to be solved automatically by SMT solvers, typically
when they requires careful inductive reasoning with precise choices at each
step. In this situation, WP allows us to generate proof goals translated in
Coq language, and to write the proof ourselves.

To learn Coq, we would recommend this tutorial:
[ce tutoriel](http://www.cis.upenn.edu/~bcpierce/sf/current/index.html).

[[information]]
| If Frama-C has been installed using the package manager of a Linux
| distribution, Coq could be automatically installed.

If one needs more information about Coq and its installation, this
page can help: [The Coq Proof Assistant](https://coq.inria.fr/).

When we want to use Coq for a proof with Frama-C, we have to select it
using the left side panel, in the WP part:

![Select the Coq proof assistant](https://zestedesavoir.com:443/media/galleries/2584/2210d1a1-8cc9-46bc-80d1-59db138ff2ad.png)

[[information]]
| The author do not know if it works under Windows.

## Why3

[[attention]]
| To the author's knowledge, it is not possible (or, at least, not easy
| at all) to install Why3 under Windows.
| The author cannot be charged for injuries that could result of such an
| operation.

Why3 is deductive proof platform developed by the LRI in Orsay. It provides
a programming language and a specification language, as well as a module that
allow to interact with a wide choice of automatic and interactive provers.
This point is the one that interest us here. WP can translate its proof
goals to the Why3 language and then use Why3 to interact with solvers.

The [Why3 website](http://why3.lri.fr/) provide all information about it.
If Opam is installed, Why3 is available using it, else, there is an another
installation procedure.

On thus website, we can find the list of
[supported provers](http://why3.lri.fr/#provers). We recommend to install
[Z3](https://github.com/Z3Prover/z3/wiki) which is developed by Microsoft
Research, and [CVC4](http://cvc4.cs.nyu.edu/web/) which is developed by many
research teams (New York University, University of Iowa, Google, CEA List).
Those two provers are very efficient and somewhat complementary.

To use these provers, the procedure is explained in the Coq part that
describes the selection of a prover for the proof. Notice that it could be
necessary to ask the detection of freshly installed provers using the
"Provers" button and then "Detect Provers" in the window that should pop.
