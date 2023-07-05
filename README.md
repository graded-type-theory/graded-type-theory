# An Agda Formalization of a Graded Modal Type Theory with a Universe and Erasure

This formalization originated as a fork of [logrel-mltt](https://github.com/mr-ohman/logrel-mltt).
The original work consisted of the following contributions:

- _A Logical Relation for Martin-Löf Type Theory in Agda_,
  code mostly written by Joakim Öhman (@mr-ohman) in 2016
  as Master's thesis supervised by Andrea Vezzosi (@Saizan)
  and Andreas Abel (@andreasabel).

  The development is described in the article
  _Decidability of Conversion for Type Theory in Type Theory_
  by Andreas Abel, Joakim Öhman and Andrea Vezzosi,
  _Proceedings of the ACM on Programming Languages_, volume 2(POPL), 2018.

- The empty type was added by Gaëtan Gilbert (@SkySkimmer, 2018).

- A unit type and Σ-types were added by Wojciech Nawrocki (@Vtec234, 2021).

- The code was refactored to use well-scoped syntax by Oskar Eriksson (@oskeri, 2021).

This work lifts the original formalization to graded modal type theory.
It is the basis of the ICFP 2023 paper
_A Graded Modal Type Theory with a Universe and Erasure, Formalized_
by Andreas Abel, Nils Anders Danielsson and Oskar Eriksson.

### Dependencies ###

This project is written in Agda.
It has been tested to be working with Agda version 2.6.3 and its standard library version 1.7.1/2.
