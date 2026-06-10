------------------------------------------------------------------------
-- Definitions related to usage restrictions controling which usage
-- rules for J and K should be used.
------------------------------------------------------------------------

import Graded.Modality

module Graded.Usage.Restrictions.JK
  {a} {M : Set a}
  (open Graded.Modality M)
  (𝕄 : Modality)
  where

open import Tools.Empty
open import Tools.PropositionalEquality
open import Tools.Product

open Modality 𝕄

-- The type JK corresponds to the eliminators J and K.

data JK : Set where
  J K : JK

-- The type JK-supported-erased-matches represents whether erased
-- matches for J and K that require the modality to have grade ω should
-- be allowed. If any kind of erased matches are allowed the modality is
-- required to have grade ω. If only "all" erased matches are allowed
-- there are no conditions on the modality.

data JK-Supported-erased-matches : Set a where
  any : ⦃ ok : Has-omega 𝕄 ⦄ → JK-Supported-erased-matches
  only-all : JK-Supported-erased-matches

-- A predicate on JK-Supported-erased-matches corresponding to
-- any erased matches being allowed.

data JK-Any-erased-matches : JK-Supported-erased-matches → Set a where
  any : ⦃ ok : Has-omega 𝕄 ⦄ → JK-Any-erased-matches any

JK-Any-erased-matches-has-omega :
  ∀ {x} → JK-Any-erased-matches x → Has-omega 𝕄
JK-Any-erased-matches-has-omega (any ⦃ ok ⦄) = ok

opaque

  -- JK-Any-erased-matches is propositional

  JK-Any-erased-matches-propositional :
    ∀ {x} → (p q : JK-Any-erased-matches x) → p ≡ q
  JK-Any-erased-matches-propositional any any = refl

opaque

  -- The grade ω given by two different proofs that J and K
  -- supports usage rules with ω are equal.

  ω≡ω :
    ∀ {x} → (ok₁ ok₂ : JK-Any-erased-matches x) →
    Has-omega.ω (JK-Any-erased-matches-has-omega ok₁) ≡
    Has-omega.ω (JK-Any-erased-matches-has-omega ok₂)
  ω≡ω any any = refl
