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
open import Tools.Nat hiding (pred)
import Tools.Reasoning.PartialOrder

open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Weakening R
open import Definition.Untyped M

private variable
  n   : Nat
  Γ   : Con Term _
  t u : Term _
  p   : M

private

  -- Some lemmas used below.

  ⊢ℕ : ⊢ ε ∙ ℕ
  ⊢ℕ  = ∙ ℕⱼ ε

  ⊢ℕℕ : ⊢ ε ∙ ℕ ∙ ℕ
  ⊢ℕℕ = ∙ ℕⱼ ⊢ℕ

  ⊢ℕℕℕ : ⊢ ε ∙ ℕ ∙ ℕ ∙ ℕ
  ⊢ℕℕℕ = ∙ ℕⱼ ⊢ℕℕ

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

⊢double : ε ⊢ double ∷ Π 𝟙 , 𝟘 ▷ ℕ ▹ ℕ
⊢double =
  lamⱼ′ Π-𝟙-𝟘 $
  natrecⱼ (var ⊢ℕ here)
    (sucⱼ (var ⊢ℕℕℕ here))
    (var ⊢ℕ here)

-- A term used to define plus

plus′ : (t u : Term n) → Term n
plus′ t u = natrec 𝟘 𝟘 𝟙 ℕ t (suc (var x0)) u

-- A program that takes two natural numbers and adds them:
-- λ m n. m + n. It might make sense to see this program as linear in
-- both arguments.

plus : Term 0
plus = lam 𝟙 $ lam 𝟙 $ plus′ (var x0) (var x1)

opaque

  -- A typing rule for plus′.

  ⊢plus′ : Γ ⊢ t ∷ ℕ → Γ ⊢ u ∷ ℕ → Γ ⊢ plus′ t u ∷ ℕ
  ⊢plus′ ⊢t ⊢u = natrecⱼ ⊢t (sucⱼ (var₀ (ℕⱼ (∙ ℕⱼ (wfTerm ⊢t))))) ⊢u

-- The term plus is well-typed.
--
-- With a certain linearity modality the term is also well-resourced,
-- see Graded.Modality.Instances.Linearity.Good.▸plus. However, with
-- another "linearity" modality the term is not well-resourced, see
-- Graded.Modality.Instances.Linearity.Bad.¬▸plus.

⊢plus : ε ⊢ plus ∷ Π 𝟙 , 𝟘 ▷ ℕ ▹ Π 𝟙 , 𝟘 ▷ ℕ ▹ ℕ
⊢plus =
  lamⱼ′ Π-𝟙-𝟘 $
  lamⱼ′ Π-𝟙-𝟘 $
  ⊢plus′ (var ⊢ℕℕ here) (var ⊢ℕℕ (there here))

opaque

  -- A term used to define f below.

  f′ : Term n → Term n → Term n
  f′ t u = natrec 𝟙 𝟘 𝟘 ℕ t (plus′ (wk₂ t) (var x1)) u

opaque

  -- An implementation of something like the following Agda code:
  --
  --   f : ℕ → ℕ → ℕ
  --   f m zero    = m
  --   f m (suc n) = m + n

  f : Term 0
  f = lam 𝟙 $ lam 𝟙 $ f′ (var x1) (var x0)

opaque
  unfolding f′

  -- A typing rule for f′.

  ⊢f′ : Γ ⊢ t ∷ ℕ → Γ ⊢ u ∷ ℕ → Γ ⊢ f′ t u ∷ ℕ
  ⊢f′ ⊢t ⊢u =
    let ⊢ℕ = ℕⱼ (∙ ℕⱼ (wfTerm ⊢t)) in
    natrecⱼ ⊢t
      (⊢plus′ (wkTerm (∷⊇→∷ʷ⊇ (step (step id)) (∙ ⊢ℕ)) ⊢t) (var₁ ⊢ℕ)) ⊢u

opaque
  unfolding f

  -- A typing rule for f.

  ⊢f :
    Π-allowed 𝟙 p →
    ε ⊢ f ∷ Π 𝟙 , p ▷ ℕ ▹ Π 𝟙 , p ▷ ℕ ▹ ℕ
  ⊢f ok =
    let ⊢ℕ = ℕⱼ ⊢ℕ in
    lamⱼ′ ok $
    lamⱼ′ ok $
    ⊢f′ (var₁ ⊢ℕ) (var₀ ⊢ℕ)

-- A term used to define pred

pred′ : Term n → Term n
pred′ t = natrec 𝟙 𝟘 𝟘 ℕ zero (var x1) t

-- A program that takes a natural numbers and returns its predecessor (truncated)
-- It might make sense to see this program as linear.

pred : Term 0
pred = lam 𝟙 $ pred′ (var x0)

-- The term pred is well-typed.

⊢pred : ε ⊢ pred ∷ Π 𝟙 , 𝟘 ▷ ℕ ▹ ℕ
⊢pred =
  lamⱼ′ Π-𝟙-𝟘 $
  natrecⱼ (zeroⱼ ⊢ℕ) (var ⊢ℕℕℕ (there here))
    (var ⊢ℕ here)
