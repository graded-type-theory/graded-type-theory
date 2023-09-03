------------------------------------------------------------------------
-- Modalities for decidable sets of natural numbers (defined under the
-- assumption of function extensionality)
------------------------------------------------------------------------

module Graded.Modality.Instances.Bounded-distributive-lattice.Set where

open import Tools.Bool
open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Sum using (_⊎_; inj₁; inj₂)

import Graded.Modality
import Graded.Modality.Instances.Bounded-distributive-lattice as
  Bounded-distributive-lattice
open import Graded.Modality.Variant lzero

-- Sets of natural numbers with decidable membership relations.

Set-ℕ : Set
Set-ℕ = Nat → Bool

private
  open module BDL = Bounded-distributive-lattice Set-ℕ
    using (Bounded-distributive-lattice)
open Graded.Modality Set-ℕ

-- An empty set.

∅ : Set-ℕ
∅ = λ _ → false

-- The set containing all natural numbers.

ℕ : Set-ℕ
ℕ = λ _ → true

-- Union.

infixr 5 _∪_

_∪_ : Set-ℕ → Set-ℕ → Set-ℕ
xs ∪ ys = λ n → xs n ∨ ys n

-- Intersection.

infixr 6 _∩_

_∩_ : Set-ℕ → Set-ℕ → Set-ℕ
xs ∩ ys = λ n → xs n ∧ ys n

-- The following lemmas are proved under the assumption that function
-- extensionality holds.

module _ (fe : Function-extensionality lzero lzero) where

  -- A "bounded distributive lattice" for Set-ℕ.

  bounded-distributive-lattice : Bounded-distributive-lattice
  bounded-distributive-lattice = record
    { _∧_                     = _∪_
    ; _∨_                     = _∩_
    ; ⊥                       = ℕ
    ; ⊤                       = ∅
    ; is-distributive-lattice = record
      { isLattice = record
        { isEquivalence = PE.isEquivalence
        ; ∨-comm        = λ xs ys → ext fe λ n →
                            ∧-comm (xs n) (ys n)
        ; ∨-assoc       = λ xs ys zs → ext fe λ n →
                            ∧-assoc (xs n) (ys n) (zs n)
        ; ∨-cong        = cong₂ _∩_
        ; ∧-comm        = λ xs ys → ext fe λ n →
                            ∨-comm (xs n) (ys n)
        ; ∧-assoc       = λ xs ys zs → ext fe λ n →
                            ∨-assoc (xs n) (ys n) (zs n)
        ; ∧-cong        = cong₂ _∪_
        ; absorptive    = (λ xs ys → ext fe λ n →
                             ∨-∧-absorptive .proj₂ (xs n) (ys n))
                        , (λ xs ys → ext fe λ n →
                             ∨-∧-absorptive .proj₁ (xs n) (ys n))
        }
      ; ∨-distribʳ-∧ = λ xs ys zs → ext fe λ n →
                         ∧-distribʳ-∨ (xs n) (ys n) (zs n)
      }
    ; ⊥≤ = λ _ → ext fe λ _ →
             refl
    ; ≤⊤ = λ xs → ext fe λ n →
             sym (∨-identityʳ (xs n))
    }

  -- A "semiring with meet" for Set-ℕ.

  semiring-with-meet : Semiring-with-meet
  semiring-with-meet = BDL.semiring-with-meet
    bounded-distributive-lattice

  -- The "semiring with meet" does not have a well-behaved zero.

  ¬-Has-well-behaved-zero : ¬ Has-well-behaved-zero semiring-with-meet
  ¬-Has-well-behaved-zero =
    Has-well-behaved-zero semiring-with-meet     →⟨ Has-well-behaved-zero.zero-product ⟩
    (∀ {xs ys} → xs ∩ ys ≡ ∅ → xs ≡ ∅ ⊎ ys ≡ ∅)  →⟨ _$ xs∩ys≡∅ ⟩
    xs ≡ ∅ ⊎ ys ≡ ∅                              →⟨ (λ { (inj₁ xs≡∅) → xs≢∅ xs≡∅; (inj₂ ys≡∅) → ys≢∅ ys≡∅ }) ⟩
    ⊥                                            □
    where
    xs : Set-ℕ
    xs 0      = false
    xs (1+ _) = true

    ys : Set-ℕ
    ys 0      = true
    ys (1+ _) = false

    xs∩ys≡∅ : xs ∩ ys ≡ ∅
    xs∩ys≡∅ = ext fe λ where
      0      → refl
      (1+ _) → refl

    xs≢∅ : xs ≢ ∅
    xs≢∅ =
      xs ≡ ∅        →⟨ cong (_$ 1) ⟩
      true ≡ false  →⟨ (λ ()) ⟩
      ⊥             □

    ys≢∅ : ys ≢ ∅
    ys≢∅ =
      ys ≡ ∅        →⟨ cong (_$ 0) ⟩
      true ≡ false  →⟨ (λ ()) ⟩
      ⊥             □

  -- Modalities for Set-ℕ.

  modality :
    (variant : Modality-variant) →
    let open Modality-variant variant in
    𝟘ᵐ-allowed ≡ false →
    Modality
  modality variant refl = BDL.modality
    variant
    bounded-distributive-lattice
    (λ ())
