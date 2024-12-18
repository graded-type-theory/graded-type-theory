------------------------------------------------------------------------
-- Weakening properties of the usage relation for Stacks.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.Variant

module Graded.Heap.Usage.Weakening
  {a} {M : Set a} {𝕄 : Modality M}
  (type-variant : Type-variant)
  (UR : Usage-restrictions 𝕄)
  (open Modality 𝕄)
  ⦃ _ : Has-nr M semiring-with-meet ⦄
  ⦃ _ : Has-factoring-nr M semiring-with-meet ⦄
  where

open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality
import Tools.Reasoning.Equivalence

open import Definition.Untyped M
open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Context.Weakening 𝕄
open import Graded.Mode 𝕄

open import Graded.Heap.Untyped type-variant UR
open import Graded.Heap.Untyped.Properties type-variant UR
open import Graded.Heap.Usage type-variant UR


private variable
  ℓ k n : Nat
  γ δ : Conₘ _
  e : Elim _
  S : Stack _
  ρ ρ′ : Wk _ _
  p q : M
  m : Mode

private opaque

  ·ᶜ-• : ∀ γ (ρ : Wk ℓ n) (ρ′ : Wk n k)
       → p ·ᶜ wkConₘ (ρ • ρ′) γ ≈ᶜ wkConₘ ρ (p ·ᶜ wkConₘ ρ′ γ)
  ·ᶜ-• {p = p} γ ρ ρ′ = begin
    p ·ᶜ wkConₘ (ρ • ρ′) γ       ≡⟨ cong (p ·ᶜ_) (wk-•ᶜ ρ ρ′) ⟩
    p ·ᶜ wkConₘ ρ (wkConₘ ρ′ γ)  ≈˘⟨ wk-·ᶜ ρ ⟩
    wkConₘ ρ (p ·ᶜ wkConₘ ρ′ γ)  ∎
    where
    open Tools.Reasoning.Equivalence Conₘ-setoid

opaque

  -- Usage of weakened eliminators.

  wk-▸ᵉ : (ρ : Wk k n) → γ ▸ᵉ[ m ] e → wkConₘ ρ γ ▸ᵉ[ m ] wkᵉ ρ e
  wk-▸ᵉ ρ (∘ₑ {γ} {m} {ρ = ρ′} ▸u) =
    subst (_▸ᵉ[ _ ] _) (≈ᶜ→≡ (·ᶜ-• γ ρ ρ′)) (∘ₑ {m = m} ▸u)
  wk-▸ᵉ ρ (fstₑ p≤𝟙) =
    subst (_▸ᵉ[ _ ] _) (sym (wk-𝟘ᶜ ρ)) (fstₑ p≤𝟙)
  wk-▸ᵉ ρ sndₑ =
    subst (_▸ᵉ[ _ ] _) (sym (wk-𝟘ᶜ ρ)) sndₑ
  wk-▸ᵉ ρ (prodrecₑ {ρ = ρ′} ▸u ok) =
    subst (_▸ᵉ[ _ ] _) (wk-•ᶜ ρ ρ′) (prodrecₑ ▸u ok)
  wk-▸ᵉ ρ (natrecₑ {ρ = ρ′} ▸z ▸s ▸A) =
    subst (_▸ᵉ[ _ ] _) (wk-•ᶜ ρ ρ′) (natrecₑ ▸z ▸s ▸A)
  wk-▸ᵉ ρ (unitrecₑ {ρ = ρ′} ▸u ok no-η) =
    subst (_▸ᵉ[ _ ] _) (wk-•ᶜ ρ ρ′) (unitrecₑ ▸u ok no-η)
  wk-▸ᵉ ρ (emptyrecₑ ok) =
    subst (_▸ᵉ[ _ ] _) (sym (wk-𝟘ᶜ ρ)) (emptyrecₑ ok)
  wk-▸ᵉ ρ (Jₑ {ρ = ρ′} ▸u) =
    subst (_▸ᵉ[ _ ] _) (wk-•ᶜ ρ ρ′) (Jₑ ▸u)
  wk-▸ᵉ ρ (Kₑ {ρ = ρ′} ▸u) =
    subst (_▸ᵉ[ _ ] _) (wk-•ᶜ ρ ρ′) (Kₑ ▸u)
  wk-▸ᵉ ρ ([]-congₑ ok) =
    subst (_▸ᵉ[ _ ] _) (sym (wk-𝟘ᶜ ρ)) ([]-congₑ ok)

opaque

  -- Usage of weakened stacks.

  wk-▸ˢ : (ρ : Wk k n) → γ ▸ˢ S → wkConₘ ρ γ ▸ˢ wkˢ ρ S
  wk-▸ˢ ρ ε = subst (_▸ˢ ε) (sym (wk-𝟘ᶜ ρ)) ε
  wk-▸ˢ {S = e ∙ S} ρ (▸e ∙ ▸S) =
    subst (_▸ˢ _) (≈ᶜ→≡ lemma)
      (subst (_ ▸ᵉ[_] _) (⌞⌟-cong (wk-∣S∣ ρ S)) (wk-▸ᵉ ρ ▸e) ∙ wk-▸ˢ ρ ▸S)
    where
    open Tools.Reasoning.Equivalence Conₘ-setoid
    lemma : wkConₘ ρ γ +ᶜ ∣ wkˢ ρ S ∣ ·ᶜ wkConₘ ρ δ ≈ᶜ wkConₘ ρ (γ +ᶜ ∣ S ∣ ·ᶜ δ)
    lemma {γ} {δ} = begin
      wkConₘ ρ γ +ᶜ ∣ wkˢ ρ S ∣ ·ᶜ wkConₘ ρ δ ≡˘⟨ cong (λ x → _ +ᶜ x ·ᶜ _) (wk-∣S∣ ρ S) ⟩
      wkConₘ ρ γ +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ δ      ≈˘⟨ +ᶜ-congˡ (wk-·ᶜ ρ) ⟩
      wkConₘ ρ γ +ᶜ wkConₘ ρ (∣ S ∣ ·ᶜ δ)    ≈˘⟨ wk-+ᶜ ρ ⟩
      wkConₘ ρ (γ +ᶜ ∣ S ∣ ·ᶜ δ)             ∎
