From the beginning of this tutorial, we have used different predicates and
logic functions provided by ACSL : `\valid`, `\valid_read`, `\separated`, `\old`
and `at`. There are others built-in predicates but we will not present them all,
the reader can refer to
[the documentation (ACSL implementation)](http://frama-c.com/download.html)
(note that everything is not necessarily supported by WP).

ACSL allows us to do something more than "just" specify our code using existing
predicates and functions. We can define our own predicates, functions,
relations, etc. Doing this, we can have more abstract specifications. It also
allows us to factor specifications (for example defining what is a valid array),
which have two pleasant consequences: our specifications are more readable and
more understandable, and we can reuse existing proofs to ease the proof of
new programs.