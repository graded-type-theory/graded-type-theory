------------------------------------------------------------------------
-- Definitions related to usage restrictions controling which usage
-- rule for natrec should be used.
------------------------------------------------------------------------

import Graded.Modality

module Graded.Usage.Restrictions.Natrec
  {a} {M : Set a}
  (open Graded.Modality M)
  (𝕄 : Modality)
  where

open import Tools.Empty
open import Tools.PropositionalEquality
open import Tools.Product

open Modality 𝕄

-- The type Natrec-mode corresponds to the different (mutually exclusive)
-- usage rules for natrec.
--
-- * Nr        : For modalities with an nr function, computing the usage
--               count.
-- * No-nr     : A usage rule that can be used for any modality.
-- * No-nr-glb : A usage rule that does not require an nr function but
--               instead that the modality has well-behaved greatest lower
--               bounds.

data Natrec-mode : Set a where
  Nr        : ⦃ has-nr : Has-nr 𝕄 ⦄ → Natrec-mode
  No-nr     : Natrec-mode
  No-nr-glb : ⦃ ok : Has-well-behaved-GLBs 𝕄 ⦄ →
              Natrec-mode

private variable
  nm : Natrec-mode

-- Predicates on Natrec-mode corresponding to each of the three usage rules.

data Natrec-mode-has-nr : Natrec-mode → Set a where
  Nr :
    ⦃ has-nr : Has-nr 𝕄 ⦄ →
    Natrec-mode-has-nr Nr

data Natrec-mode-no-nr : Natrec-mode → Set a where
  No-nr : Natrec-mode-no-nr No-nr

data Natrec-mode-no-nr-glb : Natrec-mode → Set a where
  No-nr-glb :
    ⦃ ok : Has-well-behaved-GLBs 𝕄 ⦄ →
    Natrec-mode-no-nr-glb No-nr-glb

-- Does the natrec mode support usage inference?

data Natrec-mode-supports-usage-inference (nm : Natrec-mode) : Set a where
  Nr :
    ⦃ has-nr : Natrec-mode-has-nr nm ⦄ →
    Natrec-mode-supports-usage-inference nm
  No-nr-glb :
    ⦃ no-nr : Natrec-mode-no-nr-glb nm ⦄ →
    ⦃ ok : Has-well-behaved-GLBs 𝕄 ⦄ →
    (∀ r z s → ∃ λ p → Greatest-lower-bound p (nrᵢ r z s)) →
    Natrec-mode-supports-usage-inference nm

-- If a natrec-mode corresponds to the usage rule using an nr function
-- then the modality has an nr function.

Natrec-mode-Has-nr :
  Natrec-mode-has-nr nm →
  Has-nr 𝕄
Natrec-mode-Has-nr (Nr ⦃ has-nr ⦄) = has-nr

-- If a natrec-mode corresponds to the usage rule using greatest lower
-- bounds then the modality has well-behaved GLBs.

Natrec-mode-Has-well-behaved-GLBs :
  Natrec-mode-no-nr-glb nm →
  Has-well-behaved-GLBs 𝕄
Natrec-mode-Has-well-behaved-GLBs (No-nr-glb ⦃ ok ⦄) = ok

opaque

  -- The predicate Natrec-mode-has-nr is propositional

  Nr-available-propositional :
    (x y : Natrec-mode-has-nr nm) → x ≡ y
  Nr-available-propositional Nr Nr = refl

-- The different usage rules for natrec are mutually exclusive:

opaque

  ¬[Nr∧No-nr] :
    Natrec-mode-has-nr nm →
    Natrec-mode-no-nr nm →
    ⊥
  ¬[Nr∧No-nr] Nr ()

opaque

  ¬[Nr∧No-nr-glb] :
    Natrec-mode-has-nr nm →
    Natrec-mode-no-nr-glb nm →
    ⊥
  ¬[Nr∧No-nr-glb] Nr ()

opaque

  ¬[No-nr∧No-nr-glb] :
      Natrec-mode-no-nr nm →
      Natrec-mode-no-nr-glb nm →
      ⊥
  ¬[No-nr∧No-nr-glb] No-nr ()

-- Natrec-mode? allows case splitting on the possible usage
-- rules for natrec in a way that brings the corresponding
-- instance argument into scope.

data Natrec-mode? (nm : Natrec-mode) : Set a where
  does-have-nr :
    ⦃ has-nr : Natrec-mode-has-nr nm ⦄ → Natrec-mode? nm
  does-not-have-nr :
    ⦃ no-nr : Natrec-mode-no-nr nm ⦄ → Natrec-mode? nm
  does-not-have-nr-glb :
    ⦃ no-nr : Natrec-mode-no-nr-glb nm ⦄ → Natrec-mode? nm

opaque

  -- Every Natrec-mode has a corresponding inhabitant of
  -- Natrec-mode?

  natrec-mode? : ∀ nm → Natrec-mode? nm
  natrec-mode? Nr = does-have-nr ⦃ Nr ⦄
  natrec-mode? No-nr = does-not-have-nr ⦃ No-nr ⦄
  natrec-mode? No-nr-glb = does-not-have-nr-glb ⦃ No-nr-glb ⦄
