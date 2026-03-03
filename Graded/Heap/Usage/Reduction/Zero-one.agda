------------------------------------------------------------------------
-- Properties of the usage relation for Heaps, Stacks and States
-- and the reduction relation with resource tracking for the Zero-one
-- mode structure.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Mode.Instances.Zero-one.Variant
import Graded.Mode.Instances.Zero-one
open import Graded.Usage.Restrictions
open import Graded.Usage.Restrictions.Natrec
open import Definition.Typed.Variant
open import Tools.Relation
open import Tools.PropositionalEquality

module Graded.Heap.Usage.Reduction.Zero-one
  {a} {M : Set a}
  {𝕄 : Modality M}
  {mode-variant : Mode-variant 𝕄}
  (type-variant : Type-variant)
  (open Graded.Mode.Instances.Zero-one mode-variant)
  (UR : Usage-restrictions 𝕄 Zero-one-isMode)
  (open Type-variant type-variant)
  (open Usage-restrictions UR)
  (open Modality 𝕄)
  (factoring-nr :
    ⦃ has-nr : Nr-available ⦄ →
    Is-factoring-nr M (Natrec-mode-Has-nr 𝕄 has-nr))
  (Unitʷ-η→ : ∀ {m p q} → Unitʷ-η → Unitrec-allowed m p q → ⌜ m ⌝ ≢ 𝟘 → p ≤ 𝟘)
  (¬Nr-not-available : ¬ Nr-not-available)
  where

open import Tools.Empty
open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product
open import Tools.Sum
import Tools.Reasoning.PartialOrder as RPo
import Tools.Reasoning.PropositionalEquality as RPe
import Tools.Reasoning.Equivalence as REq

open import Definition.Untyped M

open import Graded.Heap.Untyped type-variant UR factoring-nr
open import Graded.Heap.Untyped.Properties type-variant UR factoring-nr
open import Graded.Heap.Reduction type-variant UR factoring-nr
open import Graded.Heap.Usage type-variant UR factoring-nr
open import Graded.Heap.Usage.Inversion type-variant UR factoring-nr
open import Graded.Heap.Usage.Properties.Zero-one type-variant UR factoring-nr
open import Graded.Heap.Usage.Reduction type-variant UR factoring-nr Unitʷ-η→ ¬Nr-not-available

open import Graded.Context 𝕄
open import Graded.Modality.Properties 𝕄
open import Graded.Restrictions.Zero-one 𝕄 mode-variant

private variable
  k : Nat
  γ δ η γ′ δ′ θ : Conₘ _
  s s′ : State _ _ _
  A B t u v w : Term _
  p p′ q q′ r : M
  ρ : Wk _ _
  H : Heap _ _
  S : Stack _

opaque

  -- Under this assumption there are four reasons why a well-resourced
  -- state can be Final:
  -- 1. It has a variable in head position pointing to a dummy entry
  --    in the heap, the stack contains an erased emptyrec and erased uses
  --    of emptyrec are allowed.
  -- 1b. It has a level of the form t ⊔ u in head position.
  -- 2. It has a value in head position, the stack is not empty and the
  --    top of the stack does not match the head.
  -- 3. It has a value in head position and the stack is empty.
  -- 4. It has a name in head position.


  ▸Final-reasons′ :
    ∀ {k} {H : Heap k _} →
    Supports-subtraction →
    (k ≢ 0 → No-erased-matches′ type-variant UR × Has-well-behaved-zero M semiring-with-meet) →
    ▸ ⟨ H , t , ρ , S ⟩ →
    Final (⟨_,_,_,_⟩ H t ρ S) →
    ((∃ λ x → t ≡ var x × H ⊢ wkVar ρ x ↦● × emptyrec 𝟘 ∈ S ×
        Emptyrec-allowed 𝟙ᵐ 𝟘) ⊎
      (∃₂ λ u v → t ≡ u supᵘ v)) ⊎
    (∃₂ λ e S′ → S ≡ e ∙ S′ × Value t × (Matching t S → ⊥)) ⊎
    Value t × S ≡ ε ⊎
    (∃ λ α → t ≡ defn α)
  ▸Final-reasons′ {ρ} ok prop ▸s f =
    let _ , _ , _ , _ , _ , _ , _ , ▸S , _ = ▸ₛ-inv ▸s in
    case ▸Final-reasons ok ▸s f of λ where
      (inj₂ x) → inj₂ x
      (inj₁ (inj₁ (x , t≡x , d , ∣S∣≡𝟘))) →
        let nem , wb-𝟘 = prop (¬erased-heap→¬↦● d)
        in  case ▸∣∣≢𝟘 nem ⦃ wb-𝟘 ⦄ ▸S of λ where
              (inj₁ ∣S∣≢𝟘) → ⊥-elim (∣S∣≢𝟘 (∣S∣≡𝟘 wb-𝟘))
              (inj₂ prop) → inj₁ (inj₁ (x , t≡x , d , prop))
      (inj₁ (inj₂ x)) → inj₁ (inj₂ x)
