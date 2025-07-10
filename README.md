# An Agda Formalization of a Graded Modal Type Theory with First-Class Universe Levels and Erasure

See `README.agda` for more information about the code.

This formalization originated as a fork of [logrel-mltt](https://github.com/mr-ohman/logrel-mltt).
The original work consisted of the following contributions:

- _A Logical Relation for Martin-Löf Type Theory in Agda_, code mostly
  written by Joakim Öhman (@mr-ohman) in 2016 as part of a master's
  thesis supervised by Andrea Vezzosi (@Saizan) and Andreas Abel
  (@andreasabel).

  That development is described in the article _Decidability of
  Conversion for Type Theory in Type Theory_ by Andreas Abel, Joakim
  Öhman and Andrea Vezzosi, _Proceedings of the ACM on Programming
  Languages_, Volume 2, Issue POPL, 2017
  ([doi:10.1145/3158111](https://doi.org/10.1145/3158111)).

- The empty type was added by Gaëtan Gilbert (@SkySkimmer, 2018).

- A unit type and Σ-types were added by Wojciech Nawrocki (@Vtec234, 2021).

- The code was refactored to use well-scoped syntax by Oskar Eriksson (@oskeri, 2021).

- The formalization was lifted to graded modal type
  theory: this is the basis of the paper _A Graded Modal Type Theory with
  a Universe and Erasure, Formalized_ by Andreas Abel, Nils Anders
  Danielsson and Oskar Eriksson, _Proceedings of the ACM on Programming
  Languages_, Volume 7, Issue ICFP, 2023
  ([doi:10.1145/3607862](https://doi.org/10.1145/3607862)).

- Identity types were added by Nils Anders Danielsson (@nad, 2023).

- A weak unit type was added by Oskar Eriksson (@oskeri, 2023).

The present work adds a universe hierarchy with first-class universe levels.

### Dependencies ###

This project is written in Agda. It has been tested to be working with
Agda version 2.7.0.1 and its standard library version 2.2.
