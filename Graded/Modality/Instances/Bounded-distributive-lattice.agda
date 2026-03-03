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
import Graded.Context
import Graded.Context.Properties
import Graded.Modality.Instances.LowerBounded as L
import Graded.Modality.Properties
import Graded.Modality.Properties.Star as Star
open import Graded.Usage.Restrictions

open import Tools.Bool using (T; false)
open import Tools.Function
open import Tools.Nat using (1+)
open import Tools.Product
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation

private variable
  p q r : M
  γ δ : Graded.Context.Conₘ _ _

-- Bounded, distributive lattices for which equality with ⊤ is
-- decidable can be turned into modalities.

modality : Modality
modality = record
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

has-star : Has-star modality
has-star = L.has-star _ ⊥ ⊥≤

opaque

  -- One can define an nr function for bounded, distributive
  -- lattices (if equality with ⊤ is decidable).

  has-nr : Has-nr modality
  has-nr = Star.has-nr modality ⦃ has-star ⦄

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

private
  module 𝕄 = Modality modality
  module MP = Graded.Modality.Properties modality
  module C = Graded.Context modality
  module CP = Graded.Context.Properties modality

opaque

  -- The addition coincides with the meet

  +≡∧ : ∀ p q → p 𝕄.+ q ≡ p 𝕄.∧ q
  +≡∧ p q = PE.refl

opaque

  -- Addition conicides with meet for contexts

  +ᶜ≈ᶜ∧ᶜ : γ C.+ᶜ δ C.≈ᶜ γ C.∧ᶜ δ
  +ᶜ≈ᶜ∧ᶜ {γ = C.ε} {δ = C.ε} = C.ε
  +ᶜ≈ᶜ∧ᶜ {γ = _ C.∙ _} {δ = _ C.∙ _} = +ᶜ≈ᶜ∧ᶜ C.∙ (+≡∧ _ _)

opaque

  -- Multiplication is increasing

  ·-increasingˡ : ∀ p q → p ≤ p 𝕄.· q
  ·-increasingˡ p q = PE.sym (absorptive .proj₂ p q)

opaque

  -- Multiplication is increasing

  ·-increasingʳ : ∀ p q → q ≤ p 𝕄.· q
  ·-increasingʳ p q = PE.trans (PE.sym (absorptive .proj₂ q p)) (cong (q ∧_) (∨-comm _ _))

opaque

  -- Multiplication is idempotent

  ·-idem : Idempotent 𝕄._·_
  ·-idem = ∨-idem

opaque

  -- Bounded, distributive lattices support Subtraction

  supports-subtraction : MP.Supports-subtraction
  supports-subtraction =
    MP.Addition≡Meet.supports-subtraction +≡∧


opaque

  -- The greatest lower bound of nrᵢ r p q is p ∧ q

  nrᵢ-glb : 𝕄.Greatest-lower-bound (p ∧ q) (𝕄.nrᵢ r p q)
  nrᵢ-glb = lemma₁ , λ q′ q′≤ → MP.∧-greatest-lower-bound (q′≤ 0)
                                 (MP.≤-trans (q′≤ 1) (MP.∧-decreasingˡ _ _))
    where
    open MP.≤-reasoning
    lemma₁ : ∀ i → p ∧ q 𝕄.≤ 𝕄.nrᵢ r p q i
    lemma₁ 0 = MP.∧-decreasingˡ _ _
    lemma₁ {p} {q} {r} (1+ i) = begin
      p ∧ q                      ≈˘⟨ ∧-congˡ (∧-idem _) ⟩
      p ∧ (q ∧ q)                ≈˘⟨ ∧-assoc _ _ _ ⟩
      (p ∧ q) ∧ q                ≈⟨ ∧-comm _ _ ⟩
      q ∧ (p ∧ q)                ≤⟨ MP.∧-monotoneʳ (lemma₁ i) ⟩
      q ∧ 𝕄.nrᵢ r p q i          ≤⟨ MP.∧-monotoneʳ (·-increasingʳ _ _) ⟩
      q ∧ (r 𝕄.· 𝕄.nrᵢ r p q i)  ≡⟨⟩
      𝕄.nrᵢ r p q (1+ i)         ∎

opaque

  -- The greatest lower bound of nrᵢᶜ r γ δ is γ ∧ᶜ δ

  nrᵢᶜ-glbᶜ : C.Greatest-lower-boundᶜ (γ C.∧ᶜ δ) (CP.nrᵢᶜ r γ δ)
  nrᵢᶜ-glbᶜ {γ = C.ε} {δ = C.ε} = CP.ε-GLB
  nrᵢᶜ-glbᶜ {γ = γ C.∙ p} {δ C.∙ q} =
    CP.GLBᶜ-pointwise′ nrᵢᶜ-glbᶜ nrᵢ-glb

opaque

  -- The greatest lower bound of nrᵢ r ⊥ p is ⊥

  nrᵢ-⊥-glb : 𝕄.Greatest-lower-bound ⊥ (𝕄.nrᵢ r ⊥ p)
  nrᵢ-⊥-glb = (λ _ → ⊥≤ _) , (λ q q≤ → q≤ 0)
