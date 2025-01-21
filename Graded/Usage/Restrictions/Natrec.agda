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

-- open import Graded.Mode 𝕄
-- open import Graded.Usage.Erased-matches
-- open import Definition.Untyped.NotParametrised

-- open import Tools.Bool
open import Tools.Empty
-- open import Tools.Function
-- open import Tools.Level
open import Tools.PropositionalEquality
open import Tools.Product
-- open import Tools.Relation
-- open import Tools.Sum hiding (sym)


open Modality 𝕄

private variable
  p p′ q r z₁ z₂ s₁ s₂ : M

-- The type Natrec-mode corresponds to the different (mutually exclusive)
-- usage rules for natrec.
--
-- * Nr        : For modalities with an nr function, computing the usage
--               count.
-- * No-nr     : A usage rule that can be used for any modality.
-- * No-nr-glb : A usage rule that does not require an nr function but
--               instead that the modality satisfies certain properties
--               about greatest lower bounds.

data Natrec-mode : Set a where
  Nr        : ⦃ Has-nr semiring-with-meet ⦄ → Natrec-mode
  No-nr     : Natrec-mode
  No-nr-glb : ⦃ Supports-GLB-for-natrec semiring-with-meet ⦄ → Natrec-mode

private variable
  nm : Natrec-mode

-- Predicates on Natrec-mode corresponding to each of the three usage rules.

data Natrec-mode-has-nr : Natrec-mode → Set a where
  Nr :
    ⦃ has-nr : Has-nr semiring-with-meet ⦄ →
    Natrec-mode-has-nr Nr

data Natrec-mode-no-nr : Natrec-mode → Set a where
  No-nr : Natrec-mode-no-nr No-nr

data Natrec-mode-no-nr-glb : Natrec-mode → Set a where
  No-nr-glb :
    ⦃ ok : Supports-GLB-for-natrec semiring-with-meet ⦄ →
    Natrec-mode-no-nr-glb No-nr-glb

instance

  Nr-has-nr :
    ⦃ has-nr : Has-nr semiring-with-meet ⦄ →
    Natrec-mode-has-nr Nr
  Nr-has-nr = Nr

  No-nr-no-nr :
    Natrec-mode-no-nr No-nr
  No-nr-no-nr = No-nr

  No-nr-glb-no-nr-glb :
   ⦃ ok : Supports-GLB-for-natrec semiring-with-meet ⦄ →
   Natrec-mode-no-nr-glb No-nr-glb
  No-nr-glb-no-nr-glb = No-nr-glb

-- If a natrec-mode corresponds to the usage rule using an nr function
-- then the modality has an nr function.

Natrec-mode-Has-nr :
  Natrec-mode-has-nr nm →
  Has-nr semiring-with-meet
Natrec-mode-Has-nr (Nr ⦃ has-nr ⦄) = has-nr


-- If a natrec-mode corresponds to the usage rule using greatest lower
-- bounds then the modality satisfies the necessary properties.

Natrec-mode-Supports-factoring :
  Natrec-mode-no-nr-glb nm →
  Supports-GLB-for-natrec semiring-with-meet
Natrec-mode-Supports-factoring (No-nr-glb ⦃ ok ⦄) = ok

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

--   Nr-available : Set a
--   Nr-available = Natrec-mode-has-nr natrec-mode

--   Nr-not-available₁ : Set a
--   Nr-not-available₁ = Natrec-mode-no-nr₁ natrec-mode

--   Nr-not-available₂ : Set a
--   Nr-not-available₂ = Natrec-mode-no-nr₂ natrec-mode

--   opaque

--     Nr-available-propositional :
--       (x y : Nr-available) → x ≡ y
--     Nr-available-propositional = lemma
--       where
--       lemma : (x y : Natrec-mode-has-nr nm) → x ≡ y
--       lemma Nr Nr = refl

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
