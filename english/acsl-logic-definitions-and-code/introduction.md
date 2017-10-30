In this part of the tutorial, we will present two important notions of ACSL:

- axiomatic definitions,
- ghost code.

In some cases, this two notions are absolutely needed to ease the process of
specification and, more importantly, proof. On one hand by forcing some
properties to be more abstract when an explicit modeling involve to much
computation during proof, on the other hand by forcing some properties to be
explicitly modeled since they are harder to reason with when they are implicit.

Using this two notions, we expose ourselves to the possibility to make our
proof irrelevant if we make mistakes writing specification with it. The first
one allows us to introduce "false" in our assumptions, or to write imprecise
definitions. The second one opens the risk to silently modify the verified
program ... making us prove another program, which is not the one we want to
prove.