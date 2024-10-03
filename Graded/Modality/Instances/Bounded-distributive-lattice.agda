------------------------------------------------------------------------
-- Bounded, distributive lattices can be turned into modalities (if
-- equality with ⊤ is decidable)
------------------------------------------------------------------------

module Graded.Modality.Instances.Bounded-distributive-lattice
  {a} (M : Set a)
  where

open import Graded.Modality M
import Graded.Modality.Instances.LowerBounded as L
open import Graded.Modality.Variant a
open import Graded.Modality.Properties.Subtraction

open import Tools.Algebra M
open import Tools.Bool using (T; false)
open import Tools.Product
open import Tools.PropositionalEquality
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation

private variable
  p q : M

-- Bounded, distributive lattices over M.

record Bounded-distributive-lattice : Set a where
  no-eta-equality
  pattern
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
-- meet" (if equality with ⊤ is decidable).

semiring-with-meet :
  (bl : Bounded-distributive-lattice) →
  let open Bounded-distributive-lattice bl in
  ((p : M) → Dec (p ≡ ⊤)) →
  Semiring-with-meet
semiring-with-meet bl@record{} is-⊤? = record
  { _+_           = _∧_
  ; _·_           = _∨_
  ; _∧_           = _∧_
  ; 𝟘             = ⊤
  ; 𝟙             = ⊥
  ; ω             = ⊥
  ; ω≤𝟙           = ⊥≤ _
  ; ω·+≤ω·ʳ       = ⊥∨∧≤⊥∨ʳ
  ; is-𝟘?         = is-⊤?
  ; +-·-Semiring  = record
    { isSemiringWithoutAnnihilatingZero = record
      { +-isCommutativeMonoid = record
        { isMonoid = record
          { isSemigroup = ∧-isSemigroup
          ; identity    = ∧-identityˡ , comm∧idˡ⇒idʳ ∧-comm ∧-identityˡ
          }
        ; comm = ∧-comm
        }
      ; *-cong = cong₂ _∨_
      ; *-assoc = ∨-assoc
      ; *-identity = ∨-identityˡ , comm∧idˡ⇒idʳ ∨-comm ∨-identityˡ
      ; distrib = ∨-distrib-∧
      }
    ; zero = ∨-zeroˡ , comm∧zeˡ⇒zeʳ ∨-comm ∨-zeroˡ
    }
  ; ∧-Semilattice = ∧-isSemilattice
  ; ·-distrib-∧   = ∨-distrib-∧
  ; +-distrib-∧   =
      ∧-distribˡ-∧ , comm∧distrˡ⇒distrʳ ∧-comm ∧-distribˡ-∧
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

  opaque

    ⊥∨∧≤⊥∨ʳ : ⊥ ∨ (p ∧ q) ≤ ⊥ ∨ q
    ⊥∨∧≤⊥∨ʳ {p} {q} =
      ⊥ ∨ (p ∧ q)              ≡⟨ ∨-identityˡ _ ⟩
      p ∧ q                    ≡˘⟨ cong (_ ∧_) (∧-idem _) ⟩
      p ∧ (q ∧ q)              ≡˘⟨ ∧-assoc _ _ _ ⟩
      (p ∧ q) ∧ q              ≡˘⟨ cong₂ _∧_ (∨-identityˡ _) (∨-identityˡ _) ⟩
      (⊥ ∨ (p ∧ q)) ∧ (⊥ ∨ q)  ∎

-- One can define natrec-star operators for bounded, distributive
-- lattices (if equality with ⊤ is decidable).

has-star :
  (bl : Bounded-distributive-lattice) →
  let open Bounded-distributive-lattice bl in
  {is-⊤? : (p : M) → Dec (p ≡ ⊤)} →
  Has-star (semiring-with-meet bl is-⊤?)
has-star bl@record{} = L.has-star _ ⊥ ⊥≤
  where
  open Bounded-distributive-lattice bl

-- Bounded, distributive lattices for which equality with ⊤ is
-- decidable can be turned into modalities (without 𝟘ᵐ).

modality :
  (variant : Modality-variant)
  (𝕃 : Bounded-distributive-lattice) →
  let open Modality-variant variant
      open Bounded-distributive-lattice 𝕃
  in
  {is-⊤? : (p : M) → Dec (p ≡ ⊤)} →
  (T 𝟘ᵐ-allowed → Has-well-behaved-zero (semiring-with-meet 𝕃 is-⊤?)) →
  Modality
modality variant 𝕃@record{} = L.isModality
  (semiring-with-meet 𝕃 _)
  ⊥
  ⊥≤
  variant
  where
  open Bounded-distributive-lattice 𝕃

opaque

  -- Bounded, distributive lattices support Subtraction

  supports-subtraction :
    (bl : Bounded-distributive-lattice) →
    let open Bounded-distributive-lattice bl in
    (_≟⊤ : (p : M) → Dec (p ≡ ⊤)) →
    Supports-subtraction (semiring-with-meet bl _≟⊤)
  supports-subtraction bl@record{} _≟⊤ =
    Addition≡Meet.supports-subtraction (semiring-with-meet bl _≟⊤)
      λ _ _ → refl
