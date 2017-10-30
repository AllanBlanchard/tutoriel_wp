In this part of the tutorial, we have seen different ACSL construct that allow
us to factor our specifications and to express general properties that can be
used by our solver to easy their work.

All techniques we have talk about are safe, since they do not *a priori* allow
us to write false or contradictory specifications. At least if the
specification only use such logic constructions and if every lemma, precondition
(at call site), every postcondition, assertion, variant and invariant is
correctly proved, the code is correct.

However, sometimes, such constructions are not enough to express all properties
we want to express about our programs. The next constructions we will see give
us some new possibilities about it, but it will be necessary to be really
careful using them since an error would allow us to introduction false
assumptions or silently modify the program we are verifying.