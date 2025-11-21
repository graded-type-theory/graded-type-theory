------------------------------------------------------------------------
-- Examples
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Mode.Instances.Zero-one.Variant
import Graded.Mode.Instances.Zero-one
open import Graded.Usage.Restrictions
open import Graded.Heap.Assumptions
open import Definition.Typed.Restrictions
open import Graded.Modality.Instances.Linearity

module Graded.Heap.Examples.Linearity
  {variant : Mode-variant linearityModality}
  (open Graded.Mode.Instances.Zero-one variant)
  (UR : Usage-restrictions linearityModality Zero-one-isMode)
  (TR : Type-restrictions linearityModality)
  (As : Assumptions UR TR)
  where

private

  𝕄 : Modality _
  𝕄 = linearityModality

open Type-restrictions TR
open Assumptions As

open import Tools.Empty
open import Tools.Function
open import Tools.Product

open import Definition.Untyped Linearity

open import Graded.Context 𝕄
open import Graded.Usage UR
open import Graded.Heap.Untyped type-variant UR factoring-nr
open import Graded.Heap.Reduction type-variant UR factoring-nr
import Graded.Heap.Examples UR TR As as Ex

opaque

  -- Evaluating fstʷ (prodʷ 𝟙 zero zero) in the heap yields the state
  -- ⟨ ε ∙ (𝟘 , zero , id) ∙ (𝟙 , zero , step id) , zero , stepn id 2 , ε ⟩.

  fstʷ⟨0,0⟩↠* :
    initial {k = 0} (Ex.fstʷ (prodʷ 𝟙 zero zero)) ↠*
    ⟨ ε ∙ (𝟘 , zero , id) ∙ (𝟙 , zero , step id) , zero , stepn id 2 , ε ⟩
  fstʷ⟨0,0⟩↠* = Ex.fstʷ⟨0,0⟩↠* 𝟙-𝟙≡𝟘

opaque

  -- fstʷ does not have a usage rule (if certain Σ-types are allowed)

  fstʷ-no-usage :
    Σʷ-allowed 𝟙 𝟘 →
    (∀ {n} {γ : Conₘ n} {t m} → γ ▸[ m ] t →
      ∃ λ δ → δ ▸[ m ] Ex.fstʷ t) →
    ⊥
  fstʷ-no-usage ok ▸fstʷ =
    case Ex.fstʷ-has-usage→𝟙≤𝟘 ok 𝟙-𝟙≡𝟘 ▸fstʷ of λ ()
