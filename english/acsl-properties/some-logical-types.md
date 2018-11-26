ACSL provides two types that will allow us to write properties or functions
without having to think about constraints due to the size of the representation
of primitive C types in memory. These types are `integer` and `real`, which
respectively represent mathematical integers and reals (that are modeled to be
as close to reality as we can, but this notion cannot be perfectly handled).

From now, we will often use integers instead of classical C `int`s. The reason
is simply that a lot of properties and definitions are true regardless the size
of the machine integer we have as input.

On the other hand, we will not talk about the differences that exist between
`real` and `float/double`. It would require to speak about precise numerical
calculus, and about proofs of programs that rely on such calculus which could
deserve an entire dedicated tutorial.