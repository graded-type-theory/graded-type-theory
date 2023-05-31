------------------------------------------------------------------------
Code related to the paper "A Graded Modal Dependent Type Theory with a
Universe and Erasure, Formalized"
------------------------------------------------------------------------

The formalization builds on a formalization originaly published by
Andreas Abel, Andrea Vezzosi and Joakim Öhman.

It consists of the following main directories:

- Tools:

A small library of useful definitions not related to the studied system.

- Definition:

The main definition of the language. These modules are parameterized by
a type of grade annotations but are otherwise agnostic to the addition
of grades.

- Graded:

The graded modal type theory. Contains the majority of our
contribution including the definition of the modality semiring and
the usage relation as well as the erasure case study. Most modules are
parameterized by a modality semiring.

README.agda contains pointers to all results and definitions mentioned
in the paper in the order they appear. Everything.agda lists all
included modules.

The code has been tested using Agda version 2.6.3 and version 1.7.2
of Agda's standard library. If these are installed, the code can be
typechecked by running

  agda Everything.agda

or

  make check

All code can be checked using flag --safe to check that no features that
can introduce consistencies are used. Running any of the two commands
above will typecheck the code using this flag, but it can also by
supplied manually:

  agda --safe Everything.agda

Additionally, all code can be typechecked using --without-K to turn of
the K axiom. This is also done automatically when running the commands
above.
