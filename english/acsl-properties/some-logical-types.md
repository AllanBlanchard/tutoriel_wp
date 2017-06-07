ACSL provides two types that will allow us to write properties or functions
without having to take about constraints due to the size of the representation
of primitive C types in memory. These types are `integer` and `real`, which
respectively represent mathematical integers and reals (that are modeled to be
as near the reality we can, but this notion cannot be perfectly handled).

From now, we will ofter use integers instead of classical C `int`s. The reason
is simply that a lot of properties and definitions are true regardless the size
of the machine integer we have in input.

On the other hand, we will not talk about the differences that exists between
`real` and `float/double`. It would require to speak about precise numerical
calculus, and about proofs of programs that rely on such calculus which could
deserve an entire dedicated tutorial.