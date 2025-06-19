------------------------------------------------------------------------
-- Some examples which are used to illustrate properties of modality
-- instances
------------------------------------------------------------------------

open import Definition.Typed.Restrictions

import Graded.Modality

module Graded.Modality.Instances.Examples
  {a} {M : Set a}
  (open Graded.Modality M)
  {𝕄 : Modality}
  (open Modality 𝕄)
  (R : Type-restrictions 𝕄)
  (open Type-restrictions R)
  -- It is assumed that "Π 𝟙 , 𝟘" is allowed.
  (Π-𝟙-𝟘 : Π-allowed 𝟙 𝟘)
  where

open import Tools.Fin
open import Tools.Function
import Tools.Reasoning.PartialOrder

open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Untyped M

private

  -- Some lemmas used below.

  ⊢ℕ : ε »⊢ ε ∙ ℕ
  ⊢ℕ  = ∙ ℕⱼ (ε ε)

  ⊢ℕℕ : ε »⊢ ε ∙ ℕ ∙ ℕ
  ⊢ℕℕ = ∙ ℕⱼ ⊢ℕ

  ⊢ℕℕℕ : ε »⊢ ε ∙ ℕ ∙ ℕ ∙ ℕ
  ⊢ℕℕℕ = ∙ ℕⱼ ⊢ℕℕ

  ⊢ℕℕℕℕ : ε »⊢ ε ∙ ℕ ∙ ℕ ∙ ℕ ∙ ℕ
  ⊢ℕℕℕℕ = ∙ ℕⱼ ⊢ℕℕℕ

-- A program that takes a natural number and adds it to itself:
-- λ n. n + n. This program should presumably not be seen as linear,
-- because the variable "n" is used twice.

double : Term 0
double = lam 𝟙 (natrec 𝟘 𝟘 𝟙 ℕ (var x0) (suc (var x0)) (var x0))

-- The term double is well-typed.
--
-- Note that the term can be given a linear type.
--
-- With a certain "linearity" modality the term is also
-- well-resourced, see
-- Graded.Modality.Instances.Linearity.Bad.▸double. However, with
-- another linearity modality the term is not well-resourced, see
-- Graded.Modality.Instances.Linearity.Good.¬▸double.

⊢double : ε » ε ⊢ double ∷ Π 𝟙 , 𝟘 ▷ ℕ ▹ ℕ
⊢double =
  lamⱼ′ Π-𝟙-𝟘 $
  natrecⱼ (var ⊢ℕ here)
    (sucⱼ (var ⊢ℕℕℕ here))
    (var ⊢ℕ here)

-- A program that takes two natural numbers and adds them:
-- λ m n. m + n. It might make sense to see this program as linear in
-- both arguments.

plus : Term 0
plus = lam 𝟙 $ lam 𝟙 $ natrec 𝟘 𝟘 𝟙 ℕ (var x0) (suc (var x0)) (var x1)

-- The term plus is well-typed.
--
-- With a certain linearity modality the term is also well-resourced,
-- see Graded.Modality.Instances.Linearity.Good.▸plus. However, with
-- another "linearity" modality the term is not well-resourced, see
-- Graded.Modality.Instances.Linearity.Bad.¬▸plus.

⊢plus : ε » ε ⊢ plus ∷ Π 𝟙 , 𝟘 ▷ ℕ ▹ Π 𝟙 , 𝟘 ▷ ℕ ▹ ℕ
⊢plus =
  lamⱼ′ Π-𝟙-𝟘 $
  lamⱼ′ Π-𝟙-𝟘 $
  natrecⱼ (var ⊢ℕℕ here)
    (sucⱼ (var ⊢ℕℕℕℕ here))
    (var ⊢ℕℕ (there here))
