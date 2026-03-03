------------------------------------------------------------------------
-- Bounded, distributive lattices can be turned into modalities (if
-- equality with ⊤ is decidable)
------------------------------------------------------------------------

import Tools.Algebra
open import Tools.PropositionalEquality as PE
open import Tools.Relation

module Graded.Modality.Instances.Bounded-distributive-lattice
  {a} (M : Set a)
  (open Tools.Algebra M)
  (bl : Bounded-distributive-lattice)
  (open Bounded-distributive-lattice bl)
  (is-⊤? : (p : M) → Dec (p ≡ ⊤))
  where

open import Graded.Modality M
import Graded.Modality.Instances.LowerBounded as L
open import Graded.Modality.Properties.Subtraction
import Graded.Modality.Properties.Star as Star

open import Tools.Bool using (T; false)
open import Tools.Product
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation

private variable
  p q : M


-- Bounded, distributive lattices can be turned into "semirings with
-- meet" (if equality with ⊤ is decidable).

semiring-with-meet : Semiring-with-meet
semiring-with-meet = record
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
  open Tools.Reasoning.PropositionalEquality

  opaque

    ∧-distribˡ-∧ : _∧_ DistributesOverˡ _∧_
    ∧-distribˡ-∧ p q r =
      p ∧ (q ∧ r)        ≡˘⟨ cong (_∧ _) (∧-idem _) ⟩
      (p ∧ p) ∧ (q ∧ r)  ≡⟨ ∧-assoc _ _ _ ⟩
      p ∧ (p ∧ (q ∧ r))  ≡˘⟨ cong (_ ∧_) (∧-assoc _ _ _) ⟩
      p ∧ ((p ∧ q) ∧ r)  ≡˘⟨ ∧-assoc _ _ _ ⟩
      (p ∧ (p ∧ q)) ∧ r  ≡⟨ cong (_∧ _) (∧-comm _ _) ⟩
      ((p ∧ q) ∧ p) ∧ r  ≡⟨ ∧-assoc _ _ _ ⟩
      (p ∧ q) ∧ (p ∧ r)  ∎

  opaque

    ∧-identityˡ : LeftIdentity ⊤ _∧_
    ∧-identityˡ p =
      ⊤ ∧ p  ≡⟨ ∧-comm _ _ ⟩
      p ∧ ⊤  ≡˘⟨ ≤⊤ _ ⟩
      p      ∎

  opaque

    ∨-zeroˡ : LeftZero ⊤ _∨_
    ∨-zeroˡ p =
      ⊤ ∨ p        ≡⟨ cong (_ ∨_) (≤⊤ _) ⟩
      ⊤ ∨ (p ∧ ⊤)  ≡⟨ cong (⊤ ∨_) (∧-comm _ _) ⟩
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

has-star : Has-star semiring-with-meet
has-star = L.has-star _ ⊥ ⊥≤

opaque

  -- One can define an nr function for bounded, distributive
  -- lattices (if equality with ⊤ is decidable).

  has-nr : Has-nr semiring-with-meet
  has-nr = Star.has-nr semiring-with-meet ⦃ has-star ⦄

opaque
  unfolding has-nr

  -- The nr function defined (implicitly) by has-nr is given by meet of the
  -- last three arguments.

  nr≡∧ :
    ∀ p r z s n →
    Has-nr.nr has-nr p r z s n ≡ z ∧ s ∧ n
  nr≡∧ p r z s n = begin
     ⊥ ∨ ((z ∧ n) ∧ (s ∧ (p ∨ n))) ≡⟨ ∨-identityˡ _ ⟩
     (z ∧ n) ∧ (s ∧ (p ∨ n))       ≡⟨ ∧-assoc _ _ _ ⟩
     z ∧ (n ∧ s ∧ (p ∨ n))         ≡˘⟨ ∧-congˡ (∧-assoc _ _ _) ⟩
     z ∧ (n ∧ s) ∧ (p ∨ n)         ≡⟨ ∧-congˡ (∧-congʳ (∧-comm _ _)) ⟩
     z ∧ (s ∧ n) ∧ (p ∨ n)         ≡⟨ ∧-congˡ (∧-assoc _ _ _) ⟩
     z ∧ s ∧ n ∧ (p ∨ n)           ≡⟨ ∧-congˡ (∧-congˡ (∧-congˡ (∨-comm _ _))) ⟩
     z ∧ s ∧ n ∧ (n ∨ p)           ≡⟨ ∧-congˡ (∧-congˡ (absorptive .proj₂ n p)) ⟩
     z ∧ s ∧ n                     ∎
    where
    open Tools.Reasoning.PropositionalEquality

-- Bounded, distributive lattices for which equality with ⊤ is
-- decidable can be turned into modalities.

modality : Modality
modality = L.isModality
  semiring-with-meet
  ⊥
  ⊥≤

opaque

  -- The addition coincides with the meet

  +≡∧ : ∀ p q → Semiring-with-meet._+_ semiring-with-meet p q ≡ Semiring-with-meet._∧_ semiring-with-meet p q
  +≡∧ p q = PE.refl

opaque

  -- Multiplication is increasing

  ·-increasingˡ : ∀ p q → p ≤ Semiring-with-meet._·_ semiring-with-meet p q
  ·-increasingˡ p q = PE.sym (absorptive .proj₂ p q)

opaque

  -- Multiplication is increasing

  ·-increasingʳ : ∀ p q → q ≤ Semiring-with-meet._·_ semiring-with-meet p q
  ·-increasingʳ p q = PE.trans (PE.sym (absorptive .proj₂ q p)) (cong (q ∧_) (∨-comm _ _))

opaque

  -- Multiplication is idempotent

  ·-idem : Idempotent (Semiring-with-meet._·_ semiring-with-meet)
  ·-idem = ∨-idem

opaque

  -- Bounded, distributive lattices support Subtraction

  supports-subtraction :
    Supports-subtraction semiring-with-meet
  supports-subtraction =
    Addition≡Meet.supports-subtraction semiring-with-meet +≡∧
