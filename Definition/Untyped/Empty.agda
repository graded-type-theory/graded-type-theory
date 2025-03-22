------------------------------------------------------------------------
-- Definitions related to Empty
------------------------------------------------------------------------

open import Graded.Modality

module Definition.Untyped.Empty
  {a} {M : Set a}
  (𝕄 : Modality M)
  where

open Modality 𝕄

open import Definition.Untyped M
open import Definition.Untyped.Properties M

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
    emptyrec 𝟘 (Π 𝟙 , 𝟘 ▷ (Unitˢ zeroᵘ) ▹ (wk1 A)) t ∘⟨ 𝟙 ⟩ starˢ zeroᵘ

opaque
  unfolding emptyrec-sink

  -- A substitution lemma for emptyrec-sink.

  emptyrec-sink-[] :
    emptyrec-sink A t [ σ ] ≡ emptyrec-sink (A [ σ ]) (t [ σ ])
  emptyrec-sink-[] {A} {t} {σ} =
    emptyrec 𝟘 (Π 𝟙 , 𝟘 ▷ Unitˢ zeroᵘ ▹ (wk1 A [ σ ⇑ ])) (t [ σ ]) ∘⟨ 𝟙 ⟩
    starˢ zeroᵘ                                                        ≡⟨ cong₃ _∘⟨_⟩_
                                                                            (cong₂ (emptyrec _)
                                                                               (cong (Π_,_▷_▹_ _ _ _) (wk1-liftSubst A))
                                                                               refl)
                                                                            refl refl ⟩
    emptyrec 𝟘 (Π 𝟙 , 𝟘 ▷ Unitˢ zeroᵘ ▹ (wk1 (A [ σ ]))) (t [ σ ]) ∘⟨ 𝟙 ⟩
    starˢ zeroᵘ                                                        ∎
