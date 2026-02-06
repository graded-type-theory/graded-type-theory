------------------------------------------------------------------------
-- Assumptions used to prove some properties of the heap semantics.
-- In particular used for Bisimilarity, Termination and Soundness.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Mode
open import Graded.Usage.Restrictions
open import Definition.Typed.Restrictions

module Graded.Heap.Assumptions
  {a b} {M : Set a} {Mode : Set b}
  {𝕄 : Modality M}
  {𝐌 : IsMode Mode 𝕄}
  (UR : Usage-restrictions 𝕄 𝐌)
  (TR : Type-restrictions 𝕄)
  (∣ε∣ : M)
  where

open Modality 𝕄
open IsMode 𝐌
open Type-restrictions TR
open Usage-restrictions UR

open import Graded.Modality.Properties.Subtraction semiring-with-meet
import Graded.Heap.Reduction
import Graded.Heap.Typed
import Graded.Heap.Untyped
import Graded.Heap.Usage
open import Graded.Usage.Restrictions.Natrec 𝕄

open import Definition.Untyped M
open import Definition.Typed TR

open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation
open import Tools.Sum

-- Assumptions that are used to prove some bisimilarity properties
-- as well as some properties elsewhere that follow from them

record Assumptions : Set (a ⊔ b) where
  field
    -- The type Level is not allowed.
    Level-not-allowed : ¬ Level-allowed
    -- The modality supports subtraction.
    subtraction-ok : Supports-subtraction
    -- An assumption related to the weak unit type when η-equality is
    -- enabled.
    Unitʷ-η→ : ∀ {m p q} → Unitʷ-η → Unitrec-allowed m p q → ⌜ m ⌝ ≢ 𝟘 → p ≤ 𝟘
    -- Either the usage rule for natrec with an nr function is used
    -- (in which case it is assumed to be factoring) or the usage rule
    -- using greatest lower bounds is used.
    natrec-mode-ok :
      (Σ Nr-available λ has-nr →
        Is-factoring-nr M (Natrec-mode-Has-nr has-nr)) ⊎
      Nr-not-available-GLB

  opaque

    -- The usage rule without nr functions and without greatest lower
    -- bounds is not used.

    ¬Nr-not-available : ¬ Nr-not-available
    ¬Nr-not-available x =
      case natrec-mode-ok of λ where
        (inj₁ (y , _)) → ¬[Nr∧No-nr] y x
        (inj₂ y) → ¬[No-nr∧No-nr-glb] x y

  opaque

    -- If the usage rule for natrec with an nr function is used then
    -- the nr funciton is factoring.

    factoring-nr :
      ⦃ has-nr : Nr-available ⦄ →
      Is-factoring-nr M (Natrec-mode-Has-nr has-nr)
    factoring-nr ⦃ has-nr ⦄ =
      case natrec-mode-ok of λ where
        (inj₁ (has-nr′ , factoring)) →
          case Nr-available-propositional has-nr has-nr′ of λ where
            refl → factoring
        (inj₂ no-nr) → ⊥-elim (¬[Nr∧No-nr-glb] has-nr no-nr)

  open Graded.Heap.Reduction type-variant UR factoring-nr ∣ε∣
  open Graded.Heap.Typed UR TR factoring-nr ∣ε∣
  open Graded.Heap.Untyped type-variant UR factoring-nr ∣ε∣
  open Graded.Heap.Usage type-variant UR factoring-nr ∣ε∣

  -- A type that is used as an assumption in some proofs

  ⊢▸Final-Reasons : ∀ {k m n} → Con Term k → Heap k m → Term n → Wk m n → Stack m → Set _
  ⊢▸Final-Reasons {k} Δ H t ρ S =
    ∀ {A : Term k} →
    Δ ⊢ₛ ⟨ H , t , ρ , S ⟩ ∷ A →
    ▸ ⟨ H , t , ρ , S ⟩ →
    Final ⟨ H , t , ρ , S ⟩ →
    Value t × S ≡ ε
