------------------------------------------------------------------------
-- Usage relations for Heaps, Stacks and States.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.Variant
open import Graded.Usage.Restrictions.Natrec

module Graded.Heap.Usage
  {a} {M : Set a} {𝕄 : Modality M}
  (type-variant : Type-variant)
  (UR : Usage-restrictions 𝕄)
  (open Usage-restrictions UR)
  (factoring-nr :
    ⦃ has-nr : Nr-available ⦄ →
    Is-factoring-nr M (Natrec-mode-Has-nr 𝕄 has-nr))
  where

open Type-variant type-variant
open Modality 𝕄

open import Tools.Nat using (Nat)
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation

open import Definition.Untyped M
open import Graded.Heap.Untyped type-variant UR factoring-nr

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Context.Weakening 𝕄
open import Graded.Modality.Nr-instances
open import Graded.Mode 𝕄
open import Graded.Usage 𝕄 UR
open import Graded.Usage.Restrictions.Instance UR

private variable
  n k ℓ : Nat
  H H′ : Heap _ _
  ρ ρ′ : Wk _ _
  γ δ η θ χ : Conₘ _
  p q q′ r : M
  A B l t t′ u u′ v z s : Term _
  S S′ : Stack _
  c : Cont _
  m : Mode
  e : Entry _ _
  s′ : Strength

-- A comparison relation for the grades in the heap.
-- H ≤ʰ p iff all grades in the heap are bounded by p.

data _≤ʰ_ : (H : Heap k n) (p : M) → Set a where
  ε : ε ≤ʰ p
  _∙_ : H ≤ʰ p → q ≤ p → H ∙ (q , t , ρ) ≤ʰ p
  _∙● : H ≤ʰ p → H ∙● ≤ʰ p

------------------------------------------------------------------------
-- Usage of heaps.

data _▸ʰ_ : (γ : Conₘ n) (H : Heap k n) → Set a where
  ε : ε ▸ʰ ε
  _∙_ : (γ +ᶜ p ·ᶜ wkConₘ ρ δ) ▸ʰ H
      → δ ▸[ ⌞ p ⌟ ] t
      → γ ∙ p ▸ʰ H ∙ (p , t , ρ)
  _∙● : γ ▸ʰ H → γ ∙ 𝟘 ▸ʰ H ∙●
  sub : γ ▸ʰ H → γ ≤ᶜ δ → δ ▸ʰ H

------------------------------------------------------------------------
-- Usage of continuations and stacks

-- Usage of continuations

data _▸ᶜ[_]_ {n : Nat} : (γ : Conₘ n) (m : Mode) (c : Cont n) → Set a where
  lowerₑ : 𝟘ᶜ ▸ᶜ[ m ] lowerₑ
  ∘ₑ : γ ▸[ m ᵐ· p ] u → p ·ᶜ wkConₘ ρ γ ▸ᶜ[ m ] ∘ₑ p u ρ
  fstₑ : (m ≡ 𝟙ᵐ → p ≤ 𝟙) → 𝟘ᶜ ▸ᶜ[ m ] fstₑ p
  sndₑ : 𝟘ᶜ ▸ᶜ[ m ] sndₑ p
  prodrecₑ : γ ∙ ⌜ m ⌝ · r · p ∙ ⌜ m ⌝ · r ▸[ m ] u → Prodrec-allowed m r p q
           → wkConₘ ρ γ ▸ᶜ[ m ] prodrecₑ r p q A u ρ
  natrecₑ : ⦃ has-nr : Nr-available ⦄
          → γ ▸[ m ] z → δ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · r ▸[ m ] s
          → θ ∙ (⌜ 𝟘ᵐ? ⌝ · q) ▸[ 𝟘ᵐ? ] A
          → wkConₘ ρ (nrᶜ p r γ δ 𝟘ᶜ) ▸ᶜ[ m ] natrecₑ p q r A z s ρ
  natrec-no-nrₑ : ⦃ no-nr : Nr-not-available-GLB ⦄
                → γ ▸[ m ] z → δ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · r ▸[ m ] s
                → θ ∙ (⌜ 𝟘ᵐ? ⌝ · q) ▸[ 𝟘ᵐ? ] A
                → Greatest-lower-boundᶜ χ (nrᵢᶜ r γ δ)
                → wkConₘ ρ χ ▸ᶜ[ m ] natrecₑ p q r A z s ρ
  unitrecₑ : γ ▸[ m ] u → Unitrec-allowed m p q → ¬ Unitʷ-η
           → wkConₘ ρ γ ▸ᶜ[ m ] unitrecₑ p q A u ρ
  emptyrecₑ : Emptyrec-allowed m p → 𝟘ᶜ ▸ᶜ[ m ] emptyrecₑ p A ρ
  Jₑ : γ ▸[ m ] u → wkConₘ ρ γ ▸ᶜ[ m ] Jₑ p q A t B u v ρ
  Kₑ : γ ▸[ m ] u → wkConₘ ρ γ ▸ᶜ[ m ] Kₑ p A t B u ρ
  []-congₑ :
    []-cong-allowed-mode s′ m → 𝟘ᶜ ▸ᶜ[ m ] []-congₑ s′ l A t u ρ

-- Usage of stacks.

data _▸ˢ_ {n : Nat} : (γ : Conₘ n) (S : Stack n) → Set a where
  ε : 𝟘ᶜ ▸ˢ ε
  ▸ˢ∙ : ∣ S ∣≡ p → δ ▸ᶜ[ ⌞ p ⌟ ] c → γ ▸ˢ S → γ +ᶜ p ·ᶜ δ ▸ˢ c ∙ S

------------------------------------------------------------------------
-- Usage of evaluation states.

data ▸_ {k n ℓ} : (s : State k n ℓ) → Set a where
  ▸ₛ : ∣ S ∣≡ p → γ ▸ʰ H → δ ▸[ ⌞ p ⌟ ] t → η ▸ˢ S →
      γ ≤ᶜ p ·ᶜ wkConₘ ρ δ +ᶜ η →
      ▸ ⟨ H , t , ρ , S ⟩
