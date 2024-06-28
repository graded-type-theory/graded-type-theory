------------------------------------------------------------------------
-- Usage relations for Heaps, Stacks and States.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.Variant
open import Tools.Bool

module Heap.Usage
  {a} {M : Set a}
  (𝕄 : Modality M)
  (type-variant : Type-variant)
  (UR : Usage-restrictions 𝕄)
  -- (erased-matches : Bool)
  (open Modality 𝕄)
  ⦃ _ : Has-nr M semiring-with-meet ⦄
  ⦃ _ : Has-factoring-nr M semiring-with-meet ⦄
  where


open import Tools.Nat using (Nat)
open import Tools.Product
open import Tools.PropositionalEquality

open import Definition.Untyped M
open import Heap.Untyped 𝕄 type-variant

open import Graded.Context 𝕄
open import Graded.Context.Weakening 𝕄
open import Graded.Modality.Properties 𝕄
open import Graded.Mode 𝕄
open import Graded.Usage 𝕄 UR

private variable
  n k ℓ : Nat
  H H′ : Heap _ _
  E E′ : Env _ _
  γ δ η θ : Conₘ _
  p q q′ r : M
  A B t t′ u u′ v z s : Term _
  S S′ : Stack _
  e : Elim _
  m : Mode
  c : Closure _ _

-- A comparison relation for the grades in the heap.
-- H ≤ʰ p iff all grades in the heap are bounded by p.

data _≤ʰ_ : (H : Heap k n) (p : M) → Set a where
  ε : ε ≤ʰ p
  _∙_ : H ≤ʰ p → q ≤ p → H ∙ (q , t , E) ≤ʰ p
  _∙● : H ≤ʰ p → H ∙● ≤ʰ p

------------------------------------------------------------------------
-- Usage of closures

data _⨾_▸ᶜ_ (γ : Conₘ n) (p : M) : (c : Closureₘ k n) → Set a where
  ▸ᶜ : γ ▸[ m ] t
     → ⌜ m ⌝ · q ≤ p
     → γ ⨾ p ▸ᶜ (⌜ m ⌝ · q , t , E)

------------------------------------------------------------------------
-- Usage of heaps.

data _▸ʰ_ : (γ : Conₘ n) (H : Heap k n) → Set a where
  ε : ε ▸ʰ ε
  _∙_ : (γ +ᶜ p ·ᶜ wkᶜ E δ) ▸ʰ H
      → δ ⨾ p ▸ᶜ (q , t , E)
      → γ ∙ p ▸ʰ H ∙ (q , t , E)
  _∙● : -- ⦃ T (not erased-matches) ⦄
        γ ▸ʰ H → γ ∙ 𝟘 ▸ʰ H ∙●

------------------------------------------------------------------------
-- Usage of eliminators and stacks

-- Usage of eliminators

data _▸ᵉ[_]_ {n : Nat} : (γ : Conₘ n) (m : Mode) (e : Elim n) → Set a where
  ∘ₑ : γ ▸[ m ᵐ· p ] u → p ·ᶜ wkᶜ E γ ▸ᵉ[ m ] ∘ₑ p u E
  fstₑ : (m ≡ 𝟙ᵐ → p ≤ 𝟙) → 𝟘ᶜ ▸ᵉ[ m ] fstₑ p
  sndₑ : 𝟘ᶜ ▸ᵉ[ m ] sndₑ p
  prodrecₑ : γ ∙ ⌜ m ⌝ · r · p ∙ ⌜ m ⌝ · r ▸[ m ] u → r ≢ 𝟘
           → wkᶜ E γ ▸ᵉ[ m ] prodrecₑ r p q A u E
  natrecₑ : γ ▸[ m ] z → δ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · r ▸[ m ] s
          → θ ∙ (⌜ 𝟘ᵐ? ⌝ · q′) ▸[ 𝟘ᵐ? ] A
          → wkᶜ E (nrᶜ p r γ δ 𝟘ᶜ) ▸ᵉ[ m ] natrecₑ p q′ r A z s E
  unitrecₑ : γ ▸[ m ] u → p ≢ 𝟘 → wkᶜ E γ ▸ᵉ[ m ] unitrecₑ p q A u E
  Jₑ : γ ▸[ m ] u → wkᶜ E γ ▸ᵉ[ m ] Jₑ p q A t B u v E
  Kₑ : γ ▸[ m ] u → wkᶜ E γ ▸ᵉ[ m ] Kₑ p A t B u E
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
γ ⨾ δ ⨾ η ▸[ m ] ⟨ H , t , E , S ⟩ =
  γ ▸ʰ H × δ ▸[ m ] t × η ▸ˢ S × (m ≤ᵐ ∣ S ∣) × γ ≤ᶜ ∣ S ∣ ·ᶜ wkᶜ E δ +ᶜ η
