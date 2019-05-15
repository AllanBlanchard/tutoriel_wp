In this part of the tutorial, we will present three important notions of ACSL:

- inductive predicates,
- axiomatic definitions,
- ghost code.

In some cases, these notions are absolutely needed to ease the process of
specification and, more importantly, proof. On one hand by forcing some
properties to be more abstract when an explicit modeling involve to much
computation during proof, on the other hand by forcing some properties to be
explicitly modeled since they are harder to reason with when they are implicit.

Using these notions, we expose ourselves to the possibility to make our
proof irrelevant if we make mistakes writing specification with it. Inductive
predicates and axiomatic definitions involve the risk to introduce "false" in
our assumptions, or to write imprecise definitions. Ghost code opens the risk
to silently modify the verified program ... making us prove another program,
which is not the one we want to prove.