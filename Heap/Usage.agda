------------------------------------------------------------------------
-- Usage relations for Heaps, Stacks and States.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.Variant
open import Tools.Bool

module Heap.Usage
  {a} {M : Set a} {𝕄 : Modality M}
  (type-variant : Type-variant)
  (UR : Usage-restrictions 𝕄)
  (erased-heap : Bool)
  (open Modality 𝕄)
  ⦃ _ : Has-nr M semiring-with-meet ⦄
  ⦃ _ : Has-factoring-nr M semiring-with-meet ⦄
  where

open Type-variant type-variant
open Usage-restrictions UR

open import Tools.Nat using (Nat)
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation

open import Definition.Untyped M
open import Heap.Untyped type-variant UR

open import Graded.Context 𝕄
open import Graded.Context.Weakening 𝕄
open import Graded.Mode 𝕄
open import Graded.Usage 𝕄 UR

private variable
  n k ℓ : Nat
  H H′ : Heap _ _
  ρ ρ′ : Wk _ _
  γ δ η θ : Conₘ _
  p q q′ r : M
  A B t t′ u u′ v z s : Term _
  S S′ : Stack _
  e : Elim _
  m : Mode
  c : Entry _ _
  s′ : Strength

-- A comparison relation for the grades in the heap.
-- H ≤ʰ p iff all grades in the heap are bounded by p.

data _≤ʰ_ : (H : Heap k n) (p : M) → Set a where
  ε : ε ≤ʰ p
  _∙_ : H ≤ʰ p → q ≤ p → H ∙ (q , t , ρ) ≤ʰ p
  _∙● : H ≤ʰ p → H ∙● ≤ʰ p

------------------------------------------------------------------------
-- Usage of closures

data _⨾_▸ᶜ_ (γ : Conₘ n) (p : M) : (c : Entryₘ k n) → Set a where
  ▸ᶜ : γ ▸[ m ] t
     → ⌜ m ⌝ · q ≤ p
     → γ ⨾ p ▸ᶜ (⌜ m ⌝ · q , t , ρ)

------------------------------------------------------------------------
-- Usage of heaps.

data _▸ʰ_ : (γ : Conₘ n) (H : Heap k n) → Set a where
  ε : ε ▸ʰ ε
  _∙_ : (γ +ᶜ p ·ᶜ wkᶜ ρ δ) ▸ʰ H
      → δ ⨾ p ▸ᶜ (q , t , ρ)
      → γ ∙ p ▸ʰ H ∙ (q , t , ρ)
  _∙● : ⦃ T erased-heap ⦄
      → γ ▸ʰ H → γ ∙ 𝟘 ▸ʰ H ∙●

------------------------------------------------------------------------
-- Usage of eliminators and stacks

-- Usage of eliminators

data _▸ᵉ[_]_ {n : Nat} : (γ : Conₘ n) (m : Mode) (e : Elim n) → Set a where
  ∘ₑ : γ ▸[ m ᵐ· p ] u → p ·ᶜ wkᶜ ρ γ ▸ᵉ[ m ] ∘ₑ p u ρ
  fstₑ : (m ≡ 𝟙ᵐ → p ≤ 𝟙) → 𝟘ᶜ ▸ᵉ[ m ] fstₑ p
  sndₑ : 𝟘ᶜ ▸ᵉ[ m ] sndₑ p
  prodrecₑ : γ ∙ ⌜ m ⌝ · r · p ∙ ⌜ m ⌝ · r ▸[ m ] u → Prodrec-allowed m r p q
           → wkᶜ ρ γ ▸ᵉ[ m ] prodrecₑ r p q A u ρ
  natrecₑ : γ ▸[ m ] z → δ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · r ▸[ m ] s
          → θ ∙ (⌜ 𝟘ᵐ? ⌝ · q′) ▸[ 𝟘ᵐ? ] A
          → wkᶜ ρ (nrᶜ p r γ δ 𝟘ᶜ) ▸ᵉ[ m ] natrecₑ p q′ r A z s ρ
  unitrecₑ : γ ▸[ m ] u → Unitrec-allowed m p q → ¬ Unitʷ-η → wkᶜ ρ γ ▸ᵉ[ m ] unitrecₑ p q A u ρ
  emptyrecₑ : Emptyrec-allowed m p → 𝟘ᶜ ▸ᵉ[ m ] emptyrecₑ p A ρ
  Jₑ : γ ▸[ m ] u → wkᶜ ρ γ ▸ᵉ[ m ] Jₑ p q A t B u v ρ
  Kₑ : γ ▸[ m ] u → wkᶜ ρ γ ▸ᵉ[ m ] Kₑ p A t B u ρ
  []-congₑ : []-cong-allowed-mode s′ m → 𝟘ᶜ ▸ᵉ[ m ] []-congₑ s′ A t u ρ
  sucₑ : 𝟘ᶜ ▸ᵉ[ m ] sucₑ

data _≤ᵐ_ : (m : Mode) (p : M) → Set a where
  𝟘ᵐ≤ᵐ𝟘 : ∀ {ok} → 𝟘ᵐ[ ok ] ≤ᵐ 𝟘
  𝟙ᵐ≤ᵐ : 𝟙ᵐ ≤ᵐ p


-- Usage of stacks.

data _▸ˢ_ {n : Nat} : (γ : Conₘ n) (S : Stack n) → Set a where
  ε : 𝟘ᶜ ▸ˢ ε
  _∙_ : (δ ▸ᵉ[ m ] e × m ≤ᵐ ∣ S ∣)→ γ ▸ˢ S → γ +ᶜ ∣ S ∣ ·ᶜ δ ▸ˢ e ∙ S

------------------------------------------------------------------------
-- Usage of evaluation states.

_⨾_⨾_▸[_]_ : (γ : Conₘ n) (δ : Conₘ ℓ) (η : Conₘ n) (m : Mode) (s : State k n ℓ) → Set a
γ ⨾ δ ⨾ η ▸[ m ] ⟨ H , t , ρ , S ⟩ =
  γ ▸ʰ H × δ ▸[ m ] t × η ▸ˢ S × (m ≤ᵐ ∣ S ∣) × γ ≤ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ δ +ᶜ η
