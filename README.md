# About this tutorial

Frama-C (FRAmework for Modular Analysis of C programs) is a set of interoperable
program analyzers for C programs. I have used this software during all my PhD
thesis and after, mostly for deductive proof using the WP plugin. So, I wrote a
tutorial that allows to learn ACSL (the specification language of Frama-C) and
the use of WP by practice, also getting some theorical rudiments about deductive
proof.

It can be used for both learning and teaching, I hope you will have some fun with it :) .

The last stable version is available on my website in
[English](https://allan-blanchard.fr/publis/frama-c-wp-tutorial-en.pdf) and in
[French](https://allan-blanchard.fr/publis/frama-c-wp-tutoriel-fr.pdf), and in
the [Releases](https://github.com/AllanBlanchard/tutoriel_wp/releases) section
on GitHub.

An online French version is available
[on Zeste de Savoir](https://zestedesavoir.com/contenus/beta/885/introduction-a-la-preuve-de-programmes-c-avec-frama-c-et-son-greffon-wp/).

A recent build from the `master` branch is available:
- [English](https://allan-blanchard.fr/publis/frama-c-wp-tutorial-master-en.pdf)
- [French](https://allan-blanchard.fr/publis/frama-c-wp-tutoriel-master-fr.pdf)

I'll try to keep these links up to date, since GitHub does not provide a simple
way to access to the last built artifacts 😠.

## Building

In order to build the files, you can use docker
```sh
docker build -t tutoriel_wp .
docker run --rm -v $PWD:/mnt -w /mnt tutoriel_wp make
```
