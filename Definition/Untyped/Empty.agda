------------------------------------------------------------------------
-- Definitions related to Empty
------------------------------------------------------------------------

open import Graded.Modality

module Definition.Untyped.Empty
  {a} {M : Set a}
  (𝕄 : Modality M)
  where

open Modality 𝕄

import Definition.Typed.Decidable.Internal.Term
import Definition.Typed.Decidable.Internal.Weakening
open import Definition.Typed.Restrictions

open import Definition.Untyped M
open import Definition.Untyped.Properties M

open import Graded.Mode

open import Tools.Nat
open import Tools.PropositionalEquality
open import Tools.Reasoning.PropositionalEquality

private variable
  n   : Nat
  A t : Term _
  σ   : Subst _ _

opaque

  -- An eliminator for the empty type which acts as a sink usage wise.

  emptyrec-sink : Term n → Term n → Term n
  emptyrec-sink A t =
    emptyrec 𝟘 (Π 𝟙 , 𝟘 ▷ Unitˢ ▹ (wk1 A)) t ∘⟨ 𝟙 ⟩ starˢ

opaque
  unfolding emptyrec-sink

  -- A substitution lemma for emptyrec-sink.

  emptyrec-sink-[] :
    emptyrec-sink A t [ σ ] ≡ emptyrec-sink (A [ σ ]) (t [ σ ])
  emptyrec-sink-[] {A} {t} {σ} =
    emptyrec 𝟘 (Π 𝟙 , 𝟘 ▷ Unitˢ ▹ (wk1 A [ σ ⇑ ])) (t [ σ ]) ∘⟨ 𝟙 ⟩
    starˢ ≡⟨ cong₃ _∘⟨_⟩_
                                                                            (cong₂ (emptyrec _)
                                                                               (cong (Π_,_▷_▹_ _ _ _) (wk1-liftSubst A))
                                                                               refl)
                                                                            refl refl ⟩
    emptyrec 𝟘 (Π 𝟙 , 𝟘 ▷ Unitˢ ▹ (wk1 (A [ σ ]))) (t [ σ ]) ∘⟨ 𝟙 ⟩
    starˢ ∎

------------------------------------------------------------------------
-- A variant of one term former, intended to be used with the internal
-- type-checker

module Internal
  {b} {Mode : Set b}
  (𝐌 : IsMode Mode 𝕄)
  (R : Type-restrictions 𝕄)
  where

  private
    module I  = Definition.Typed.Decidable.Internal.Term 𝐌 R
    module IW = Definition.Typed.Decidable.Internal.Weakening 𝐌 R

  private variable
    c     : I.Constants
    Aᵢ tᵢ : I.Term _ _
    γ     : I.Contexts _

  -- A variant of emptyrec-sink, intended to be used with the internal
  -- type-checker.

  emptyrec-sinkᵢ : I.Term c n → I.Term c n → I.Term c n
  emptyrec-sinkᵢ A t =
    I.emptyrec I.𝟘 (I.Π I.𝟙 , I.𝟘 ▷ I.Unit I.𝕤 ▹ IW.wk[ 1 ] A) t
      I.∘⟨ I.𝟙 ⟩ I.star I.𝕤

  opaque
    unfolding emptyrec-sink

    -- A translation lemma for emptyrec-sinkᵢ.

    ⌜emptyrec-sinkᵢ⌝ :
      I.⌜ emptyrec-sinkᵢ Aᵢ tᵢ ⌝ γ ≡
      emptyrec-sink (I.⌜ Aᵢ ⌝ γ) (I.⌜ tᵢ ⌝ γ)
    ⌜emptyrec-sinkᵢ⌝ = refl
