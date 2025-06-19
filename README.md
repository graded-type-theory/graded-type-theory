# An Agda Formalization of a Graded Modal Type Theory with a Universe Hierarchy and Erasure

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

This work lifts the original formalization to graded modal type
theory. It is the basis of the paper _A Graded Modal Type Theory with
a Universe and Erasure, Formalized_ by Andreas Abel, Nils Anders
Danielsson and Oskar Eriksson, _Proceedings of the ACM on Programming
Languages_, Volume 7, Issue ICFP, 2023
([doi:10.1145/3607862](https://doi.org/10.1145/3607862)).

The present version of the code contains changes made after
publication of the ICFP paper, see [README.agda](README.agda). Some
highlights:

- Identity types were added by Nils Anders Danielsson (@nad, 2023).

- A weak unit type was added by Oskar Eriksson (@oskeri, 2023).

- A universe hierarchy was added by Nils Anders Danielsson and Ondřej
  Kubánek (@nad and @kubaneko, 2024).

- Top-level definitions and opacity were added by Nils Anders
  Danielsson and Eve Geng (@nad and @phantamanta44, 2025).

### Dependencies ###

This project is written in Agda. It has been tested to be working with
Agda version 2.8.0 and its standard library version 2.3.
