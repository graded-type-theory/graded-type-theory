------------------------------------------------------------------------
-- Usage relations for Heaps, Stacks and States.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.Variant

module Heap.Usage
  {a} {M : Set a}
  (𝕄 : Modality M)
  (type-variant : Type-variant)
  (UR : Usage-restrictions 𝕄)
  (open Modality 𝕄)
  ⦃ _ : Has-nr M semiring-with-meet ⦄
  ⦃ _ : Has-factoring-nr M semiring-with-meet ⦄
  where


open import Tools.Bool
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
  n k : Nat
  H H′ : Heap _
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

data _≤ʰ_ : (H : Heap n) (p : M) → Set a where
  ε : ε ≤ʰ p
  _∙_ : H ≤ʰ p → q ≤ p → H ∙ (q , t , E) ≤ʰ p

------------------------------------------------------------------------
-- Usage of closures

data _⨾_▸ᶜ[_]_ (γ : Conₘ n) (p : M) (m : Mode) :
               (c : Closureₘ k n) → Set a where
  ▸ᶜ : γ ▸[ m ] t
     → ⌜ m ⌝ · q ≤ p
     → γ ⨾ p ▸ᶜ[ m ] (⌜ m ⌝ · q , t , E)

-- Usage of closures where the mode is 𝟙ᵐ

▸ᶜ¹ : γ ▸ t
    → q ≤ p
    → γ ⨾ p ▸ᶜ[ 𝟙ᵐ ] (q , t , E)
▸ᶜ¹ {γ = γ} {t} {q} {p} {E = E} ▸t q≤p =
  let 𝟙q≡q = ·-identityˡ q
  in  subst (λ x → γ ⨾ p ▸ᶜ[ 𝟙ᵐ ] (x , t , E)) 𝟙q≡q
       (▸ᶜ ▸t (≤-trans (≤-reflexive 𝟙q≡q) q≤p))

-- Usage of closures where the mode is the same as the grade

▸ᶜᵖ : γ ▸[ ⌞ p ⌟ ] t
    → γ ⨾ p ▸ᶜ[ ⌞ p ⌟ ] (p , t , E)
▸ᶜᵖ {γ = γ} {p} {t} {E = E} ▸t =
  subst (λ x → γ ⨾ x ▸ᶜ[ ⌞ p ⌟ ] (x , t , E))
    ⌜⌞⌟⌝· (▸ᶜ ▸t ≤-refl)

------------------------------------------------------------------------
-- Usage of heaps.

data _▸ʰ_ : (γ : Conₘ n) (H : Heap n) → Set a where
  ε : ε ▸ʰ ε
  _∙_ : (γ +ᶜ p ·ᶜ wkᶜ E δ) ▸ʰ H
      → δ ⨾ p ▸ᶜ[ m ] (q , t , E)
      → γ ∙ p ▸ʰ H ∙ (q , t , E)

------------------------------------------------------------------------
-- Usage of eliminators and stacks

-- Usage of eliminators

data _▸ᵉ_ {n : Nat} : (γ : Conₘ n) (e : Elim n) → Set a where
  ∘ₑ : γ ▸[ ⌞ p ⌟ ] u → p ·ᶜ wkᶜ E γ ▸ᵉ ∘ₑ p u E
  fstₑ : p ≤ 𝟙 → 𝟘ᶜ ▸ᵉ fstₑ p
  sndₑ : 𝟘ᶜ ▸ᵉ sndₑ p
  prodrecₑ : γ ∙ r · p ∙ r ▸ u → r ≢ 𝟘
           → wkᶜ E γ ▸ᵉ prodrecₑ r p q A u E
  natrecₑ : γ ▸ z → δ ∙ p ∙ r ▸ s
          → θ ∙ (⌜ 𝟘ᵐ? ⌝ · q′) ▸[ 𝟘ᵐ? ] A
          → wkᶜ E (nrᶜ p r γ δ 𝟘ᶜ) ▸ᵉ natrecₑ p q′ r A z s E
  unitrecₑ : γ ▸ u → p ≢ 𝟘 → wkᶜ E γ ▸ᵉ unitrecₑ p q A u E
  Jₑ : γ ▸ u → wkᶜ E γ ▸ᵉ Jₑ p q A t B u v E
  Kₑ : γ ▸ u → wkᶜ E γ ▸ᵉ Kₑ p A t B u E
  sucₑ : 𝟘ᶜ ▸ᵉ sucₑ

-- Usage of stacks.

data _▸ˢ_ {n : Nat} : (γ : Conₘ n) (S : Stack n) → Set a where
  ε : 𝟘ᶜ ▸ˢ ε
  _∙_ : δ ▸ᵉ e → γ ▸ˢ S → γ +ᶜ ∣ S ∣ ·ᶜ δ ▸ˢ e ∙ S

------------------------------------------------------------------------
-- Usage of evaluation states.

_⨾_⨾_▸_ : (γ : Conₘ n) (δ : Conₘ k) (η : Conₘ n) (s : State n k) → Set a
γ ⨾ δ ⨾ η ▸ ⟨ H , t , E , S ⟩ =
  γ ▸ʰ H × δ ▸ t × η ▸ˢ S × γ ≤ᶜ ∣ S ∣ ·ᶜ wkᶜ E δ +ᶜ η
