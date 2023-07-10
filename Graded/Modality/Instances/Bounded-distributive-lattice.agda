------------------------------------------------------------------------
-- Bounded, distributive lattices can be turned into modalities
------------------------------------------------------------------------

module Graded.Modality.Instances.Bounded-distributive-lattice
  {a} (M : Set a)
  where

open import Graded.Modality M
import Graded.Modality.Instances.LowerBounded as L
open import Graded.Mode.Restrictions

open import Tools.Algebra M
open import Tools.Bool using (false)
open import Tools.Product
open import Tools.PropositionalEquality hiding (⊥)
import Tools.Reasoning.PropositionalEquality

-- Bounded, distributive lattices over M.

record Bounded-distributive-lattice : Set a where
  infixr 40 _∧_ _∨_
  field
    -- Meet.
    _∧_ : M → M → M

    -- Join.
    _∨_ : M → M → M

    -- The least element.
    ⊥ : M

    -- The greatest element.
    ⊤ : M

    -- Join and meet form a distributive lattice.
    is-distributive-lattice : IsDistributiveLattice _∨_ _∧_

  open IsDistributiveLattice is-distributive-lattice public
  open DistributiveLattice is-distributive-lattice public

  -- An induced ordering relation.

  _≤_ : M → M → Set a
  p ≤ q = p ≡ p ∧ q

  field
    -- ⊥ is the least element.
    ⊥≤ : ∀ p → ⊥ ≤ p

    -- ⊤ is the greatest element.
    ≤⊤ : ∀ p → p ≤ ⊤

-- Bounded, distributive lattices can be turned into "semirings with
-- meet".

semiring-with-meet :
  Bounded-distributive-lattice → Semiring-with-meet
semiring-with-meet bl = record
  { _+_           = _∧_
  ; _·_           = _∨_
  ; _∧_           = _∧_
  ; 𝟘             = ⊤
  ; 𝟙             = ⊥
  ; +-·-Semiring  = record
    { isSemiringWithoutAnnihilatingZero = record
      { +-isCommutativeMonoid = record
        { isMonoid = record
          { isSemigroup = ∧-isSemigroup
          ; identity    = ∧-identityˡ , comm+idˡ⇒idʳ ∧-comm ∧-identityˡ
          }
        ; comm = ∧-comm
        }
      ; *-isMonoid = record
        { isSemigroup = ∨-isSemigroup
        ; identity    = ∨-identityˡ , comm+idˡ⇒idʳ ∨-comm ∨-identityˡ
        }
      ; distrib = ∨-distrib-∧
      }
    ; zero = ∨-zeroˡ , comm+zeˡ⇒zeʳ ∨-comm ∨-zeroˡ
    }
  ; ∧-Semilattice = ∧-isSemilattice
  ; ·-distrib-∧   = ∨-distrib-∧
  ; +-distrib-∧   =
      ∧-distribˡ-∧ , comm+distrˡ⇒distrʳ ∧-comm ∧-distribˡ-∧
  }
  where
  open Bounded-distributive-lattice bl
  open Tools.Reasoning.PropositionalEquality

  ∧-distribˡ-∧ : _∧_ DistributesOverˡ _∧_
  ∧-distribˡ-∧ p q r =
    p ∧ (q ∧ r)        ≡˘⟨ cong (_∧ _) (∧-idem _) ⟩
    (p ∧ p) ∧ (q ∧ r)  ≡⟨ ∧-assoc _ _ _ ⟩
    p ∧ (p ∧ (q ∧ r))  ≡˘⟨ cong (_ ∧_) (∧-assoc _ _ _) ⟩
    p ∧ ((p ∧ q) ∧ r)  ≡˘⟨ ∧-assoc _ _ _ ⟩
    (p ∧ (p ∧ q)) ∧ r  ≡⟨ cong (_∧ _) (∧-comm _ _) ⟩
    ((p ∧ q) ∧ p) ∧ r  ≡⟨ ∧-assoc _ _ _ ⟩
    (p ∧ q) ∧ (p ∧ r)  ∎

  ∧-identityˡ : LeftIdentity ⊤ _∧_
  ∧-identityˡ p =
    ⊤ ∧ p  ≡⟨ ∧-comm _ _ ⟩
    p ∧ ⊤  ≡˘⟨ ≤⊤ _ ⟩
    p      ∎

  ∨-identityˡ : LeftIdentity ⊥ _∨_
  ∨-identityˡ p =
    ⊥ ∨ p        ≡⟨ cong (_∨ _) (⊥≤ _) ⟩
    (⊥ ∧ p) ∨ p  ≡⟨ cong (_∨ _) (∧-comm _ _) ⟩
    (p ∧ ⊥) ∨ p  ≡⟨ ∨-comm _ _ ⟩
    p ∨ (p ∧ ⊥)  ≡⟨ ∨-absorbs-∧ _ _ ⟩
    p            ∎

  ∨-zeroˡ : LeftZero ⊤ _∨_
  ∨-zeroˡ p =
    ⊤ ∨ p        ≡⟨ cong (_ ∨_) (≤⊤ _) ⟩
    ⊤ ∨ (p ∧ ⊤)  ≡⟨ cong (_ ∨_) (∧-comm _ _) ⟩
    ⊤ ∨ (⊤ ∧ p)  ≡⟨ ∨-absorbs-∧ _ _ ⟩
    ⊤            ∎

-- Bounded, distributive lattices can be turned into modalities.

modality : Bounded-distributive-lattice → Modality
modality bl = L.isModality
  (semiring-with-meet bl)
  ⊥
  ⊥≤
  (𝟘ᵐ-allowed-if false)
  (λ ())
  where
  open Bounded-distributive-lattice bl
