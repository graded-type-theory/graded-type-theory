------------------------------------------------------------------------
-- Some properties related to usage and the strong variant of Erased
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Mode
open import Graded.Usage.Restrictions

module Graded.Derived.Erased.Usage.Eta
  {a b} {M : Set a} {Mode : Set b}
  {𝕄 : Modality M}
  {𝐌 : IsMode Mode 𝕄}
  (R : Usage-restrictions 𝕄 𝐌)
  where

open Modality 𝕄
open IsMode 𝐌

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Usage R
open import Graded.Usage.Inversion R
open import Graded.Usage.Properties R

open import Definition.Untyped M
open import Definition.Untyped.Erased.Eta 𝕄

open import Tools.Bool
open import Tools.Empty
open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation

private variable
  t : Term _
  γ   : Conₘ _
  m   : Mode
  ok  : T _

------------------------------------------------------------------------
-- Usage rules

opaque

  -- A usage rule for erased.

  ▸erased′ :
    (Trivialᵐ → 𝟘 ≤ 𝟙) →
    γ ▸[ 𝟘ᵐ ] t → 𝟘ᶜ ▸[ 𝟘ᵐ ] erased t
  ▸erased′ {γ} {t} hyp ▸t =
    sub (fstₘ 𝟙ᵐ (▸-cong (PE.sym (ᵐ·-zeroʳ _)) (▸-𝟘 ▸t) ) (ᵐ·-zeroʳ _)
          (hyp ∘→ ⌜𝟘ᵐ⌝≢𝟘→)) 𝟘≤
    where
    open ≤ᶜ-reasoning
    𝟘≤ : 𝟘ᶜ ≤ᶜ ⌜ 𝟘ᵐ ⌝ ·ᶜ γ
    𝟘≤ = case trivialᵐ? of λ where
          (yes 𝟙ᵐ≡𝟘ᵐ) → begin
            𝟘ᶜ          ≈˘⟨ ·ᶜ-zeroˡ _ ⟩
            𝟘 ·ᶜ γ      ≤⟨ ·ᶜ-monotoneˡ (hyp 𝟙ᵐ≡𝟘ᵐ) ⟩
            𝟙 ·ᶜ γ      ≈˘⟨ ·ᶜ-congʳ (⌜𝟘ᵐ⌝′ 𝟙ᵐ≡𝟘ᵐ) ⟩
            ⌜ 𝟘ᵐ ⌝ ·ᶜ γ ∎
          (no 𝟙ᵐ≢𝟘ᵐ) → begin
            𝟘ᶜ          ≈˘⟨ ·ᶜ-zeroˡ _ ⟩
            𝟘 ·ᶜ γ      ≈˘⟨ ·ᶜ-congʳ (⌜𝟘ᵐ⌝ 𝟙ᵐ≢𝟘ᵐ) ⟩
            ⌜ 𝟘ᵐ ⌝ ·ᶜ γ ∎

opaque

  -- Another usage rule for erased.

  ▸erased : ¬ Trivialᵐ → γ ▸[ 𝟘ᵐ ] t → 𝟘ᶜ ▸[ 𝟘ᵐ ] erased t
  ▸erased {γ} 𝟙ᵐ≢𝟘ᵐ ▸t = ▸erased′ (⊥-elim ∘→ (𝟙ᵐ≢𝟘ᵐ $_)) ▸t

------------------------------------------------------------------------
-- Inversion lemmas for usage

opaque

  -- An inversion lemma for erased.

  inv-usage-erased′ :
    γ ▸[ m ] erased t →
    ∃ λ δ → ⌜ 𝟘ᵐ ⌝ ·ᶜ δ ▸[ 𝟘ᵐ ] t × γ ≤ᶜ ⌜ 𝟘ᵐ ⌝ ·ᶜ δ × m PE.≡ 𝟘ᵐ
  inv-usage-erased′ {γ = γ} ▸[] =
    case inv-usage-fst ▸[] of λ where
      (invUsageFst {δ = δ} m PE.refl ▸t γ≤ _) →
          _
        , ▸-𝟘 ▸t
         , (begin
             γ           ≤⟨ γ≤ ⟩
             δ           ≤⟨ ▸ᵐ (▸-cong (ᵐ·-zeroʳ _) ▸t) ⟩
             ⌜ 𝟘ᵐ ⌝ ·ᶜ δ ∎)
        , ᵐ·-zeroʳ _
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset

opaque

  -- Another inversion lemma for erased.

  inv-usage-erased :
    ¬ Trivialᵐ →
    γ ▸[ m ] erased t →
    𝟘ᶜ ▸[ 𝟘ᵐ ] t × γ ≤ᶜ 𝟘ᶜ × m PE.≡ 𝟘ᵐ
  inv-usage-erased {γ = γ} 𝟙ᵐ≢𝟘ᵐ ▸[] =
    let _ , ▸t , γ≤ , m≡ = inv-usage-erased′ ▸[]
        ≈ᶜ𝟘ᶜ = ≈ᶜ-trans (·ᶜ-congʳ (⌜𝟘ᵐ⌝ 𝟙ᵐ≢𝟘ᵐ)) (·ᶜ-zeroˡ _)
    in  sub ▸t (≤ᶜ-reflexive (≈ᶜ-sym ≈ᶜ𝟘ᶜ))
      , ≤ᶜ-trans γ≤ (≤ᶜ-reflexive ≈ᶜ𝟘ᶜ)
      , m≡
