------------------------------------------------------------------------
-- Weakening properties of the usage relation for Stacks.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Mode
open import Graded.Usage.Restrictions
open import Definition.Typed.Variant
open import Graded.Usage.Restrictions.Natrec

module Graded.Heap.Usage.Weakening
  {a b} {M : Set a} {Mode : Set b}
  {𝕄 : Modality M}
  {𝐌 : IsMode Mode 𝕄}
  (type-variant : Type-variant)
  (UR : Usage-restrictions 𝕄 𝐌)
  (open Usage-restrictions UR)
  (factoring-nr :
    ⦃ has-nr : Nr-available ⦄ →
    Is-factoring-nr M (Natrec-mode-Has-nr 𝕄 has-nr))
  (∣ε∣ : M)
  where

open import Tools.Nat
open import Tools.PropositionalEquality
import Tools.Reasoning.Equivalence

open import Definition.Untyped M
open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Context.Weakening 𝕄

open import Graded.Heap.Untyped type-variant UR factoring-nr ∣ε∣
open import Graded.Heap.Untyped.Properties type-variant UR factoring-nr ∣ε∣
open import Graded.Heap.Usage type-variant UR factoring-nr ∣ε∣


private variable
  ℓ k n : Nat
  γ δ : Conₘ _
  c : Cont _
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

  -- Usage of weakened continuations.

  wk-▸ᶜ : (ρ : Wk k n) → γ ▸ᶜ[ m ] c → wkConₘ ρ γ ▸ᶜ[ m ] wkᶜ ρ c
  wk-▸ᶜ ρ lowerₑ =
    subst (_▸ᶜ[ _ ] _) (sym (wk-𝟘ᶜ ρ)) lowerₑ
  wk-▸ᶜ ρ (∘ₑ {γ} {m} {ρ = ρ′} ▸u) =
    subst (_▸ᶜ[ _ ] _) (≈ᶜ→≡ (·ᶜ-• γ ρ ρ′)) (∘ₑ {m = m} ▸u)
  wk-▸ᶜ ρ (fstₑ p≤𝟙) =
    subst (_▸ᶜ[ _ ] _) (sym (wk-𝟘ᶜ ρ)) (fstₑ p≤𝟙)
  wk-▸ᶜ ρ sndₑ =
    subst (_▸ᶜ[ _ ] _) (sym (wk-𝟘ᶜ ρ)) sndₑ
  wk-▸ᶜ ρ (prodrecₑ {ρ = ρ′} ▸u ok) =
    subst (_▸ᶜ[ _ ] _) (wk-•ᶜ ρ ρ′) (prodrecₑ ▸u ok)
  wk-▸ᶜ ρ (natrecₑ {ρ = ρ′} ▸z ▸s ▸A) =
    subst (_▸ᶜ[ _ ] _) (wk-•ᶜ ρ ρ′) (natrecₑ ▸z ▸s ▸A)
  wk-▸ᶜ ρ (natrec-no-nrₑ {ρ = ρ′} ▸z ▸s ▸A χ-glb) =
    subst (_▸ᶜ[ _ ] _) (wk-•ᶜ ρ ρ′) (natrec-no-nrₑ ▸z ▸s ▸A χ-glb)
  wk-▸ᶜ ρ (unitrecₑ {ρ = ρ′} ▸u ok no-η) =
    subst (_▸ᶜ[ _ ] _) (wk-•ᶜ ρ ρ′) (unitrecₑ ▸u ok no-η)
  wk-▸ᶜ ρ (emptyrecₑ ok) =
    subst (_▸ᶜ[ _ ] _) (sym (wk-𝟘ᶜ ρ)) (emptyrecₑ ok)
  wk-▸ᶜ ρ (Jₑ {ρ = ρ′} ▸u) =
    subst (_▸ᶜ[ _ ] _) (wk-•ᶜ ρ ρ′) (Jₑ ▸u)
  wk-▸ᶜ ρ (Kₑ {ρ = ρ′} ▸u) =
    subst (_▸ᶜ[ _ ] _) (wk-•ᶜ ρ ρ′) (Kₑ ▸u)
  wk-▸ᶜ ρ ([]-congₑ ok) =
    subst (_▸ᶜ[ _ ] _) (sym (wk-𝟘ᶜ ρ)) ([]-congₑ ok)

opaque

  -- Usage of weakened stacks.

  wk-▸ˢ : (ρ : Wk k n) → γ ▸ˢ S → wkConₘ ρ γ ▸ˢ wkˢ ρ S
  wk-▸ˢ ρ ε = subst (_▸ˢ ε) (sym (wk-𝟘ᶜ ρ)) ε
  wk-▸ˢ {S = e ∙ S} ρ (▸ˢ∙ ∣S∣≡ ▸e ▸S) =
    subst (_▸ˢ _) (≈ᶜ→≡ lemma)
      (▸ˢ∙ (wk-∣∣ ∣S∣≡) (wk-▸ᶜ ρ ▸e) (wk-▸ˢ ρ ▸S))
    where
    open Tools.Reasoning.Equivalence Conₘ-setoid
    lemma : wkConₘ ρ γ +ᶜ p ·ᶜ wkConₘ ρ δ ≈ᶜ wkConₘ ρ (γ +ᶜ p ·ᶜ δ)
    lemma {γ} {p} {δ} = begin
      wkConₘ ρ γ +ᶜ p ·ᶜ wkConₘ ρ δ      ≈˘⟨ +ᶜ-congˡ (wk-·ᶜ ρ) ⟩
      wkConₘ ρ γ +ᶜ wkConₘ ρ (p ·ᶜ δ)    ≈˘⟨ wk-+ᶜ ρ ⟩
      wkConₘ ρ (γ +ᶜ p ·ᶜ δ)             ∎
