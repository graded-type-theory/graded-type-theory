------------------------------------------------------------------------
-- Definitions related to usage restrictions related to the grade ω
------------------------------------------------------------------------

import Graded.Modality

module Graded.Usage.Restrictions.Omega
  {a} {M : Set a}
  (open Graded.Modality M)
  (𝕄 : Modality)
  where

open import Tools.Empty
open import Tools.PropositionalEquality
open import Tools.Product
open import Tools.Relation

open Modality 𝕄

-- The type Usage-with-or-without-omega represents whether usage rules
-- that require the modality to have grade ω should be allowed.

data Usage-with-or-without-omega : Set a where
  with-ω    : ⦃ ok : Has-omega 𝕄 ⦄ → Usage-with-or-without-omega
  without-ω : Usage-with-or-without-omega

-- A predicate on Usage-with-or-without-omega corresponding to allowing
-- rules with ω.

data Usage-with-omega : Usage-with-or-without-omega → Set a where
  with-ω : ⦃ ok : Has-omega 𝕄 ⦄ → Usage-with-omega with-ω

Usage-with-omega-has-omega :
  ∀ {x} → Usage-with-omega x → Has-omega 𝕄
Usage-with-omega-has-omega (with-ω ⦃ ok ⦄) = ok

opaque

  -- Usage-with-omega is propistional

  Usage-with-omega-propositional :
    ∀ {x} → (p q : Usage-with-omega x) → p ≡ q
  Usage-with-omega-propositional with-ω with-ω = refl

opaque

  -- The grade ω given by two different proofs that ω is supported
  -- are equal

  ω≡ω :
    ∀ {x} (ok₁ ok₂ : Usage-with-omega x) →
    Has-omega.ω (Usage-with-omega-has-omega ok₁) ≡
    Has-omega.ω (Usage-with-omega-has-omega ok₂)
  ω≡ω with-ω with-ω = refl

opaque

  ω≡ω′ :
    ∀ {x y} → x ≡ y →
    (ok₁ : Usage-with-omega x) (ok₂ : Usage-with-omega y) →
    Has-omega.ω (Usage-with-omega-has-omega ok₁) ≡
    Has-omega.ω (Usage-with-omega-has-omega ok₂)
  ω≡ω′ refl = ω≡ω

opaque

  -- The predicate Usage-with-omega is decidable

  Usage-with-omega? : ∀ {x} → Dec (Usage-with-omega x)
  Usage-with-omega? {x = with-ω} = yes with-ω
  Usage-with-omega? {x = without-ω} = no (λ ())
