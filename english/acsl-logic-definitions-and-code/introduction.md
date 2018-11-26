In this part of the tutorial, we will present two important notions of ACSL:

- axiomatic definitions,
- ghost code.

In some cases, these two notions are absolutely needed to ease the process of
specification and, more importantly, proof. On one hand, they force some
properties to be more abstract when an explicit modeling would involve too much
computation during proof, on the other hand, they force some properties to be
explicitly modeled since they are harder to reason about when they are implicit.

Using these two notions, we expose ourselves to the possibility to make our
proof irrelevant if we make mistakes writing specification with it. The first
one allows us to introduce "false" in our assumptions, or to write imprecise
definitions. The second one opens the risk to silently modify the verified
program ... making us prove another program, which is not the one we want to
prove.