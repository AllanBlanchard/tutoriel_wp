It is time to enter the heart of the matter. Rather than starting with basic
notions of the C language, as we would do for a tutorial about C, we will start
with functions. First because it is necessary to be able to write functions
before starting this tutorial (to be able to prove that a code is correct, being
able to write it correct is required), and then because it will allow us to
directly prove some programs.

After this part about functions, we will on the opposite focus on simple notions
like assignments or conditional structures, to understand how our tool really
works.

In order to be able to prove that a code is valid, we first need to specify what
we expect of it. Building the proof of our program consists in ensuring that the
code we wrote corresponds to the specification that describes its job. As we
previously said, Frama-C provides the ACSL language to let the developer write
contracts about each function (but that is not its only purpose, as we will see
later).