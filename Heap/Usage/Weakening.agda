------------------------------------------------------------------------
-- Weakening properties of the usage relation for Stacks.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.Variant
open import Tools.Bool

module Heap.Usage.Weakening
  {a} {M : Set a} {𝕄 : Modality M}
  (type-variant : Type-variant)
  (UR : Usage-restrictions 𝕄)
  (erased-heap : Bool)
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

open import Heap.Untyped type-variant UR
open import Heap.Untyped.Properties type-variant UR
open import Heap.Usage type-variant UR erased-heap


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
       → p ·ᶜ wkᶜ (ρ • ρ′) γ ≈ᶜ wkᶜ ρ (p ·ᶜ wkᶜ ρ′ γ)
  ·ᶜ-• {p = p} γ ρ ρ′ = begin
    p ·ᶜ wkᶜ (ρ • ρ′) γ       ≡⟨ cong (p ·ᶜ_) (wk-•ᶜ ρ ρ′) ⟩
    p ·ᶜ wkᶜ ρ (wkᶜ ρ′ γ)  ≈˘⟨ wk-·ᶜ ρ ⟩
    wkᶜ ρ (p ·ᶜ wkᶜ ρ′ γ)  ∎
    where
    open Tools.Reasoning.Equivalence Conₘ-setoid

opaque

  -- Usage of weakened eliminators.

  wk-▸ᵉ : (ρ : Wk k n) → γ ▸ᵉ[ m ] e → wkᶜ ρ γ ▸ᵉ[ m ] wkᵉ ρ e
  wk-▸ᵉ ρ (∘ₑ {γ} {m} {E} ▸u) =
    subst (_▸ᵉ[ _ ] _) (≈ᶜ→≡ (·ᶜ-• γ ρ E)) (∘ₑ {m = m} ▸u)
  wk-▸ᵉ ρ (fstₑ p≤𝟙) =
    subst (_▸ᵉ[ _ ] _) (sym (wk-𝟘ᶜ ρ)) (fstₑ p≤𝟙)
  wk-▸ᵉ ρ sndₑ =
    subst (_▸ᵉ[ _ ] _) (sym (wk-𝟘ᶜ ρ)) sndₑ
  wk-▸ᵉ ρ (prodrecₑ {E} ▸u ok) =
    subst (_▸ᵉ[ _ ] _) (wk-•ᶜ ρ E) (prodrecₑ ▸u ok)
  wk-▸ᵉ ρ (natrecₑ {E} ▸z ▸s ▸A) =
    subst (_▸ᵉ[ _ ] _) (wk-•ᶜ ρ E) (natrecₑ ▸z ▸s ▸A)
  wk-▸ᵉ ρ (unitrecₑ {E} ▸u ok no-η) =
    subst (_▸ᵉ[ _ ] _) (wk-•ᶜ ρ E) (unitrecₑ ▸u ok no-η)
  wk-▸ᵉ ρ (Jₑ {E} ▸u) =
    subst (_▸ᵉ[ _ ] _) (wk-•ᶜ ρ E) (Jₑ ▸u)
  wk-▸ᵉ ρ (Kₑ {E} ▸u) =
    subst (_▸ᵉ[ _ ] _) (wk-•ᶜ ρ E) (Kₑ ▸u)
  wk-▸ᵉ ρ ([]-congₑ ok) =
    subst (_▸ᵉ[ _ ] _) (sym (wk-𝟘ᶜ ρ)) ([]-congₑ ok)
  wk-▸ᵉ ρ sucₑ =
    subst (_▸ᵉ[ _ ] _) (sym (wk-𝟘ᶜ ρ)) sucₑ

opaque

  -- Usage of weakened stacks.

  wk-▸ˢ : (ρ : Wk k n) → γ ▸ˢ S → wkᶜ ρ γ ▸ˢ wkˢ ρ S
  wk-▸ˢ ρ ε = subst (_▸ˢ ε) (sym (wk-𝟘ᶜ ρ)) ε
  wk-▸ˢ {S = e ∙ S} ρ ((▸e , m≤) ∙ ▸S) =
    subst (_▸ˢ _) (≈ᶜ→≡ lemma) ((wk-▸ᵉ ρ ▸e , subst (_ ≤ᵐ_) (wk-∣S∣ ρ S) m≤) ∙ wk-▸ˢ ρ ▸S)
    where
    open Tools.Reasoning.Equivalence Conₘ-setoid
    lemma : wkᶜ ρ γ +ᶜ ∣ wkˢ ρ S ∣ ·ᶜ wkᶜ ρ δ ≈ᶜ wkᶜ ρ (γ +ᶜ ∣ S ∣ ·ᶜ δ)
    lemma {γ} {δ} = begin
      wkᶜ ρ γ +ᶜ ∣ wkˢ ρ S ∣ ·ᶜ wkᶜ ρ δ ≡˘⟨ cong (λ x → _ +ᶜ x ·ᶜ _) (wk-∣S∣ ρ S) ⟩
      wkᶜ ρ γ +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ δ      ≈˘⟨ +ᶜ-congˡ (wk-·ᶜ ρ) ⟩
      wkᶜ ρ γ +ᶜ wkᶜ ρ (∣ S ∣ ·ᶜ δ)    ≈˘⟨ wk-+ᶜ ρ ⟩
      wkᶜ ρ (γ +ᶜ ∣ S ∣ ·ᶜ δ)          ∎
