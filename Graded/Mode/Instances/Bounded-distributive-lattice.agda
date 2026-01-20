------------------------------------------------------------------------
-- Bounded, distributive lattices can be used as modes.
------------------------------------------------------------------------

import Tools.Algebra
open import Tools.Relation
open import Tools.PropositionalEquality as PE

module Graded.Mode.Instances.Bounded-distributive-lattice
  {a} {M : Set a}
  (open Tools.Algebra M)
  (bl : Bounded-distributive-lattice)
  (open Bounded-distributive-lattice bl)
  (is-⊤? : (p : M) → Dec (p ≡ ⊤))
  where

open import Graded.Modality M
open import Graded.Modality.Instances.Bounded-distributive-lattice M bl is-⊤?

private
  -- The modality for the lattice
  𝕄 : Modality
  𝕄 = modality

module 𝕄 = Modality 𝕄

open import Tools.Function
open import Tools.Product
import Tools.Reasoning.PropositionalEquality

open import Graded.Mode M 𝕄

private variable
  p q : M

------------------------------------------------------------------------
-- The mode structure

bounded-distributive-lattice-isMode : IsMode
bounded-distributive-lattice-isMode = record
   { _·ᵐ_ = 𝕄._·_
   ; 𝟘ᵐ = ⊤
   ; 𝟙ᵐ = ⊥
   ; ⌞_⌟ = idᶠ
   ; ⌜_⌝ = idᶠ
   ; ·ᵐ-IdempotentCommutativeMonoid = record
     { isCommutativeMonoid = record
       { isMonoid = record
         { isSemigroup = record
           { isMagma = record
             { isEquivalence = PE.isEquivalence
             ; ∙-cong = 𝕄.·-cong
             }
           ; assoc = 𝕄.·-assoc
           }
         ; identity = 𝕄.·-identity }
       ; comm = ∨-comm
       }
     ; idem = ∨-idem
     }
   ; ·ᵐ-zero = 𝕄.·-zero
   ; ⌞⌜⌝⌟ = λ _ → PE.refl
   ; ⌜·ᵐ⌝ = λ _ → PE.refl
   ; ⌞⌟·ᵐ = PE.refl
   ; ·⌜⌞⌟⌝ = ∨-idem _
   ; ⌜⌞⌟⌝· = ∨-idem _
   ; ≤⌜⌝· = λ {p _ m} _ _ → begin
       p           ≡˘⟨ ∧-absorbs-∨ _ _ ⟩
       p ∧ (p ∨ m) ≡⟨ cong (p ∧_) (∨-comm _ _) ⟩
       p ∧ (m ∨ p) ∎
   ; is-𝟘ᵐ? = is-⊤?
   ; ⌜𝟘ᵐ⌝ = λ _ → PE.refl
   ; ⌞+⌟-decreasingˡ = PE.sym (∨-absorbs-∧ _ _)
   ; ⌞∧⌟-decreasingˡ = PE.sym (∨-absorbs-∧ _ _)
   }
   where
   open Tools.Reasoning.PropositionalEquality

open IsMode bounded-distributive-lattice-isMode public

------------------------------------------------------------------------
-- Properties of the mode structure

opaque

  -- The order relations for grades and modes are equivalent

  ≤⇔≤ᵐ : p 𝕄.≤ q ⇔ p ≤ᵐ q
  ≤⇔≤ᵐ {p} {q} =
    (λ p≤q → begin
      q           ≡˘⟨ ∨-absorbs-∧ q p ⟩
      q ∨ (q ∧ p) ≡⟨ ∨-congˡ (∧-comm q p) ⟩
      q ∨ (p ∧ q) ≡˘⟨ ∨-congˡ p≤q ⟩
      q ∨ p       ∎) ,
    λ p≤ᵐq → begin
      p           ≡˘⟨ ∧-absorbs-∨ p q ⟩
      p ∧ (p ∨ q) ≡⟨ ∧-congˡ (∨-comm p q) ⟩
      p ∧ (q ∨ p) ≡˘⟨ ∧-congˡ p≤ᵐq ⟩
      p ∧ q       ∎
    where
    open Tools.Reasoning.PropositionalEquality
