------------------------------------------------------------------------
-- The usage relation.
------------------------------------------------------------------------

import Graded.Modality
open import Graded.Usage.Restrictions

module Graded.Usage
  {a} {M : Set a}
  (open Graded.Modality M)
  (𝕄 : Modality)
  (R : Usage-restrictions M)
  where

open Modality 𝕄
open Usage-restrictions R

open import Graded.Context 𝕄
open import Graded.Modality.Dedicated-star 𝕄
open import Graded.Mode 𝕄
open import Definition.Untyped M hiding (_∙_)

open import Tools.Fin
open import Tools.Nat using (Nat)
open import Tools.Nullary
open import Tools.PropositionalEquality using (_≡_)

infix 10 _▸[_]_

private
  variable
    n : Nat
    p q r : M
    γ δ γ′ η θ χ : Conₘ n
    A F G : Term n
    s t u z : Term n
    x : Fin n
    m m′ : Mode
    b : BinderMode

-- Modality context inference (for modalities with natrec-star
-- operators).

infix 50 ⌈_⌉

mutual
  ⌈_⌉ :
    ⦃ has-star : Has-star semiring-with-meet ⦄ →
    Term n → Mode → Conₘ n
  ⌈ var x ⌉ m = 𝟘ᶜ , x ≔ ⌜ m ⌝
  ⌈ U ⌉ _ = 𝟘ᶜ
  ⌈ ΠΣ⟨ _ ⟩ p , q ▷ F ▹ G ⌉ m = ⌈ F ⌉ (m ᵐ· p) +ᶜ tailₘ (⌈ G ⌉ m)
  ⌈ lam p t ⌉ m = tailₘ (⌈ t ⌉ m)
  ⌈ t ∘⟨ p ⟩ u ⌉ m = ⌈ t ⌉ m +ᶜ p ·ᶜ ⌈ u ⌉ (m ᵐ· p)
  ⌈ prod Σᵣ p t u ⌉ m = p ·ᶜ ⌈ t ⌉ (m ᵐ· p) +ᶜ ⌈ u ⌉ m
  ⌈ prod Σₚ p t u ⌉ m = p ·ᶜ ⌈ t ⌉ (m ᵐ· p) ∧ᶜ ⌈ u ⌉ m
  ⌈ fst p t ⌉ m = ⌈ t ⌉ m
  ⌈ snd p t ⌉ m = ⌈ t ⌉ m
  ⌈ prodrec r p _ A t u ⌉ m =
    r ·ᶜ ⌈ t ⌉ (m ᵐ· r) +ᶜ tailₘ (tailₘ (⌈ u ⌉ m))
  ⌈ ℕ ⌉ _ = 𝟘ᶜ
  ⌈ zero ⌉ _ = 𝟘ᶜ
  ⌈ suc t ⌉ m = ⌈ t ⌉ m
  ⌈ natrec p _ r A z s n ⌉ m =
    let γ  = ⌈ z ⌉ m
        δ′ = ⌈ s ⌉ m
        η  = ⌈ n ⌉ m
        δ  = tailₘ (tailₘ δ′)
    in  (γ ∧ᶜ η) ⊛ᶜ (δ +ᶜ p ·ᶜ η) ▷ r
  ⌈ Unit ⌉ _ = 𝟘ᶜ
  ⌈ star ⌉ _ = 𝟘ᶜ
  ⌈ Empty ⌉ _ = 𝟘ᶜ
  ⌈ emptyrec p A e ⌉ m = p ·ᶜ ⌈ e ⌉ (m ᵐ· p)

-- Well-usage of variables
data _◂_∈_  : (x : Fin n) (p : M) (γ : Conₘ n) → Set a where
  here  :                       x0 ◂ p ∈ γ ∙ p
  there : (h : x ◂ p ∈ γ) → (x +1) ◂ p ∈ γ ∙ q

open import Graded.Modality.Dedicated-star.Instance

-- Well-usage relation for terms.
--
-- The definition is partly based on Bob Atkey's "Syntax and Semantics
-- of Quantitative Type Theory".
data _▸[_]_ {n : Nat} : (γ : Conₘ n) → Mode → Term n → Set a where
  Uₘ        : 𝟘ᶜ ▸[ m ] U
  ℕₘ        : 𝟘ᶜ ▸[ m ] ℕ
  Emptyₘ    : 𝟘ᶜ ▸[ m ] Empty
  Unitₘ     : 𝟘ᶜ ▸[ m ] Unit

  ΠΣₘ       : γ ▸[ m ᵐ· p ] F
            → δ ∙ ⌜ m ⌝ · q ▸[ m ] G
            → γ +ᶜ δ ▸[ m ] ΠΣ⟨ b ⟩ p , q ▷ F ▹ G

  var       : (𝟘ᶜ , x ≔ ⌜ m ⌝) ▸[ m ] var x

  lamₘ      : γ ∙ ⌜ m ⌝ · p ▸[ m ] t
            → γ ▸[ m ] lam p t

  _∘ₘ_      : γ ▸[ m ] t
            → δ ▸[ m ᵐ· p ] u
            → γ +ᶜ p ·ᶜ δ ▸[ m ] t ∘⟨ p ⟩ u

  prodᵣₘ    : γ ▸[ m ᵐ· p ] t
            → δ ▸[ m ] u
            → p ·ᶜ γ +ᶜ δ ▸[ m ] prodᵣ p t u

  prodₚₘ   : γ ▸[ m ᵐ· p ] t
           → δ ▸[ m ] u
           → p ·ᶜ γ ∧ᶜ δ ▸[ m ] prodₚ p t u

  -- Note that either p ≤ 𝟙 or m′ ≡ 𝟘ᵐ
  fstₘ      : ∀ m
            → γ ▸[ m ᵐ· p ] t
            → m ᵐ· p ≡ m′
            → (m′ ≡ 𝟙ᵐ → p ≤ 𝟙)
            → γ ▸[ m′ ] fst p t

  sndₘ      : γ ▸[ m ] t
            → γ ▸[ m ] snd p t

  prodrecₘ  : γ ▸[ m ᵐ· r ] t
            → δ ∙ ⌜ m ⌝ · r · p ∙ ⌜ m ⌝ · r ▸[ m ] u
            → η ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] A
            → Prodrec-allowed r p q
            → r ·ᶜ γ +ᶜ δ ▸[ m ] prodrec r p q A t u

  zeroₘ     : 𝟘ᶜ ▸[ m ] zero
  sucₘ      : γ ▸[ m ] t
            → γ ▸[ m ] suc t

  -- A usage rule for natrec which applies if a dedicated natrec-star
  -- operator is available.
  natrecₘ   : ∀ {n} ⦃ has-star : Dedicated-star ⦄
            → γ ▸[ m ] z
            → δ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · r ▸[ m ] s
            → η ▸[ m ] n
            → θ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] A
            → (γ ∧ᶜ η) ⊛ᶜ (δ +ᶜ p ·ᶜ η) ▷ r ▸[ m ] natrec p q r A z s n

  -- A usage rule for natrec which applies if a dedicated natrec-star
  -- operator is not available.
  natrec-no-starₘ :
            ∀ {n} ⦃ no-star : No-dedicated-star ⦄
            → γ ▸[ m ] z
            → δ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · r ▸[ m ] s
            → η ▸[ m ] n
            → θ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] A
            → χ ≤ᶜ γ ∧ᶜ η ∧ᶜ (δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ χ)
            → χ ▸[ m ] natrec p q r A z s n

  emptyrecₘ : γ ▸[ m ᵐ· p ] t
            → δ ▸[ 𝟘ᵐ? ] A
            → p ·ᶜ γ ▸[ m ] emptyrec p A t

  starₘ     : 𝟘ᶜ ▸[ m ] star

  sub       : γ ▸[ m ] t
            → δ ≤ᶜ γ
            → δ ▸[ m ] t
