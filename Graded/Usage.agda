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
open import Graded.Modality.Dedicated-nr 𝕄
open import Graded.Mode 𝕄
open import Definition.Untyped M hiding (_∙_)

open import Tools.Bool using (T)
open import Tools.Fin
open import Tools.Nat using (Nat)
open import Tools.Product
open import Tools.PropositionalEquality using (_≡_)
open import Tools.Sum using (_⊎_)

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

-- Modality context inference (for modalities with nr functions).

infix 50 ⌈_⌉

mutual
  ⌈_⌉ :
    ⦃ has-nr : Has-nr semiring-with-meet ⦄ →
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
  ⌈ prodrec r _ _ _ t u ⌉ m =
    r ·ᶜ ⌈ t ⌉ (m ᵐ· r) +ᶜ tailₘ (tailₘ (⌈ u ⌉ m))
  ⌈ ℕ ⌉ _ = 𝟘ᶜ
  ⌈ zero ⌉ _ = 𝟘ᶜ
  ⌈ suc t ⌉ m = ⌈ t ⌉ m
  ⌈ natrec p _ r _ z s n ⌉ m =
    nrᶜ p r (⌈ z ⌉ m) (tailₘ (tailₘ (⌈ s ⌉ m))) (⌈ n ⌉ m)
  ⌈ Unit ⌉ _ = 𝟘ᶜ
  ⌈ star ⌉ _ = 𝟘ᶜ
  ⌈ Empty ⌉ _ = 𝟘ᶜ
  ⌈ emptyrec p _ t ⌉ m = p ·ᶜ ⌈ t ⌉ (m ᵐ· p)

-- Well-usage of variables
data _◂_∈_  : (x : Fin n) (p : M) (γ : Conₘ n) → Set a where
  here  :                       x0 ◂ p ∈ γ ∙ p
  there : (h : x ◂ p ∈ γ) → (x +1) ◂ p ∈ γ ∙ q

open import Graded.Modality.Dedicated-nr.Instance

-- Well-usage relation for terms.
--
-- The definition is partly based on Robert Atkey's "Syntax and
-- Semantics of Quantitative Type Theory".
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

  -- A usage rule for natrec which applies if a dedicated nr function
  -- ("natrec usage function") is available.
  natrecₘ   : ∀ {n} ⦃ has-nr : Dedicated-nr ⦄
            → γ ▸[ m ] z
            → δ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · r ▸[ m ] s
            → η ▸[ m ] n
            → θ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] A
            → nrᶜ p r γ δ η ▸[ m ] natrec p q r A z s n

  -- A usage rule for natrec which applies if a dedicated nr function
  -- is not available.
  --
  -- There are four inequality assumptions:
  --
  -- * Two are always required to hold. These assumptions are (at the
  --   time of writing) for instance used to prove the natrec-zero and
  --   natrec-suc cases of the subject reduction lemma
  --   Graded.Reduction.usagePresTerm.
  --
  -- * The assumption χ ≤ᶜ η is only required to hold if the
  --   modality's zero is well-behaved. This assumption is (at the
  --   time of writing) used, together with the two unrestricted
  --   assumptions, to prove the fundamental lemma
  --   Graded.Erasure.LogicalRelation.Fundamental.Fundamental.fundamental
  --   (among other things). The statement of this lemma includes the
  --   assumption that the modality's zero is well-behaved.
  --
  -- * The assumption χ ≤ᶜ δ is only required to hold if 𝟘ᵐ is
  --   allowed. This assumption is used to prove the substitution
  --   lemma Graded.Substitution.Properties.substₘ-lemma.
  --
  -- Note that this rule may not always be appropriate. See
  -- Graded.Modality.Instances.Linearity.Bad.No-dedicated-nr,
  -- Graded.Modality.Instances.Affine.Bad.No-dedicated-nr and
  -- Graded.Modality.Instances.Linear-or-affine.Bad.No-dedicated-nr
  -- for some examples.
  natrec-no-nrₘ :
            ∀ {n} ⦃ no-nr : No-dedicated-nr ⦄
            → γ ▸[ m ] z
            → δ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · r ▸[ m ] s
            → η ▸[ m ] n
            → θ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] A
            → χ ≤ᶜ γ
            → (T 𝟘ᵐ-allowed →
               χ ≤ᶜ δ)
            → (⦃ 𝟘-well-behaved :
                   Has-well-behaved-zero semiring-with-meet ⦄ →
               χ ≤ᶜ η)
            → χ ≤ᶜ δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ χ
            → χ ▸[ m ] natrec p q r A z s n

  emptyrecₘ : γ ▸[ m ᵐ· p ] t
            → δ ▸[ 𝟘ᵐ? ] A
            → p ·ᶜ γ ▸[ m ] emptyrec p A t

  starₘ     : 𝟘ᶜ ▸[ m ] star

  sub       : γ ▸[ m ] t
            → δ ≤ᶜ γ
            → δ ▸[ m ] t
