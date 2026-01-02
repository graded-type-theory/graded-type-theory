# An Agda Formalization of a Graded Modal Type Theory with Erasure, First-Class Universe Levels and Opaque Definitions

## Project history

This formalization originated as a fork of
[logrel-mltt](https://github.com/mr-ohman/logrel-mltt). That work
consisted of the following contributions:

- _A Logical Relation for Martin-Löf Type Theory in Agda_, code mostly
  written by Joakim Öhman (@mr-ohman) in 2016 as part of a master's
  thesis supervised by Andrea Vezzosi (@Saizan) and Andreas Abel
  (@andreasabel).

  That development is described in the article _Decidability of
  Conversion for Type Theory in Type Theory_, Andreas Abel, Joakim
  Öhman and Andrea Vezzosi, _Proceedings of the ACM on Programming
  Languages_, Volume 2, Issue POPL, 2017
  ([doi:10.1145/3158111](https://doi.org/10.1145/3158111)).

- The empty type was added by Gaëtan Gilbert (@SkySkimmer, 2018).

- A unit type and Σ-types were added by Wojciech Nawrocki (@Vtec234, 2021).

- The code was refactored to use well-scoped syntax by Oskar Eriksson (@oskeri, 2021).

The formalization was lifted to graded modal type theory: this is the
basis of the paper _A Graded Modal Type Theory with a Universe and
Erasure, Formalized_, Andreas Abel, Nils Anders Danielsson and Oskar
Eriksson, _Proceedings of the ACM on Programming Languages_, Volume 7,
Issue ICFP, 2023
([doi:10.1145/3607862](https://doi.org/10.1145/3607862)). See also
[README.Graded-type-theory](README/Graded-type-theory.agda).

Later other additions were made. Some highlights:

- Identity types were added by Nils Anders Danielsson (@nad, 2023).

- A weak unit type was added by Oskar Eriksson (@oskeri, 2023).

- A universe hierarchy with first-class universe levels was added by
  Nils Anders Danielsson, Naïm Camille Favier and Ondřej Kubánek
  (@nad, @ncfavier and @kubaneko, 2024-2025), see
  [README.First-class-universe-levels](README/First-class-universe-levels.lagda.md)
  for more details. This addition is also described in the paper
  _Normalisation for First-Class Universe Levels_, Nils Anders
  Danielsson, Naïm Camille Favier and Ondřej Kubánek, _Proceedings of
  the ACM on Programming Languages_, Volume 10, Issue POPL, 2026
  ([doi:10.1145/3776645](https://doi.org/10.1145/3776645)).

- Top-level definitions and opacity were added by Nils Anders
  Danielsson and Eve Geng (@nad and @phantamanta44, 2025), see
  [README.Opaque-definitions](README/Opaque-definitions.lagda.md) for more
  details. This addition is also described in the paper _A
  Formalization of Opaque Definitions for a Dependent Type Theory_,
  Nils Anders Danielsson and Eve Geng, _Proceedings of the 10th ACM
  SIGPLAN International Workshop on Type-Driven Development (TyDe
  '25)_, 2025
  ([doi:10.1145/3759538.3759653](https://doi.org/10.1145/3759538.3759653)).

## Dependencies ##

This project is written in Agda. It has been tested to be working with
Agda version 2.8.0 and its standard library version 2.3.
