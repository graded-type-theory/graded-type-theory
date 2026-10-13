------------------------------------------------------------------------
-- Definitions related to the parts of the configuration that are
-- related to ω grades
------------------------------------------------------------------------

import Graded.Modality

module Configuration-types.Omega
  {a} {M : Set a}
  (open Graded.Modality M)
  (𝕄 : Modality)
  where

open import Tools.Empty
open import Tools.PropositionalEquality
open import Tools.Product
open import Tools.Relation

open Modality 𝕄

-- Can parts of the language that require the grade ω be allowed? In
-- that case, how should ω be defined?

data With-or-without-omega : Set a where
  with-ω    : ⦃ ok : Has-omega 𝕄 ⦄ → With-or-without-omega
  without-ω : With-or-without-omega

-- If With-omega w holds, then w allows omega.

data With-omega : With-or-without-omega → Set a where
  with-ω : ⦃ ok : Has-omega 𝕄 ⦄ → With-omega with-ω

With-omega→Has-omega :
  ∀ {x} → With-omega x → Has-omega 𝕄
With-omega→Has-omega (with-ω ⦃ ok ⦄) = ok

opaque

  -- With-omega is propositional.

  With-omega-propositional :
    ∀ {x} → (p q : With-omega x) → p ≡ q
  With-omega-propositional with-ω with-ω = refl

opaque

  -- The grade ω given by two different proofs that ω is supported
  -- are equal

  ω≡ω :
    ∀ {x} (ok₁ ok₂ : With-omega x) →
    Has-omega.ω (With-omega→Has-omega ok₁) ≡
    Has-omega.ω (With-omega→Has-omega ok₂)
  ω≡ω with-ω with-ω = refl

opaque

  ω≡ω′ :
    ∀ {x y} → x ≡ y →
    (ok₁ : With-omega x) (ok₂ : With-omega y) →
    Has-omega.ω (With-omega→Has-omega ok₁) ≡
    Has-omega.ω (With-omega→Has-omega ok₂)
  ω≡ω′ refl = ω≡ω

opaque

  -- The predicate With-omega is decidable

  With-omega? : ∀ {x} → Dec (With-omega x)
  With-omega? {x = with-ω} = yes with-ω
  With-omega? {x = without-ω} = no (λ ())
