open import Definition.Modality

module Definition.Modality.Usage
  {a} {M : Set a} (𝕄 : Modality M) where

open Modality 𝕄

open import Definition.Modality.Context 𝕄
open import Definition.Mode 𝕄
open import Definition.Untyped M hiding (_∙_)

open import Tools.Fin
open import Tools.Nat
open import Tools.PropositionalEquality as PE using (_≈_)

infix 10 _▸[_]_

private
  variable
    n : Nat
    p q r : M
    γ δ γ′ η θ : Conₘ n
    A F : Term n
    G : Term (1+ n)
    t u : Term n
    x : Fin n
    m m′ : Mode
    b : BinderMode
    s : SigmaMode

-- Well-usage of variables
data _◂_∈_  : (x : Fin n) (p : M) (γ : Conₘ n) → Set a where
  here  :                       x0 ◂ p ∈ γ ∙ p
  there : (h : x ◂ p ∈ γ) → (x +1) ◂ p ∈ γ ∙ q

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
            → Binder b p q
            → γ +ᶜ δ ▸[ m ] ΠΣ⟨ b ⟩ p , q ▷ F ▹ G

  var       : (𝟘ᶜ , x ≔ ⌜ m ⌝) ▸[ m ] var x

  lamₘ      : ∀ {t}
            → γ ∙ ⌜ m ⌝ · p ▸[ m ] t
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
            → m ᵐ· p PE.≡ m′
            → (m′ PE.≡ 𝟙ᵐ → p ≤ 𝟙)
            → γ ▸[ m′ ] fst p t

  sndₘ      : γ ▸[ m ] t
            → γ ▸[ m ] snd p t

  prodrecₘ  : γ ▸[ m ᵐ· r ] t
            → δ ∙ ⌜ m ⌝ · r · p ∙ ⌜ m ⌝ · r ▸[ m ] u
            → η ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] A
            → Prodrec r p q
            → r ·ᶜ γ +ᶜ δ ▸[ m ] prodrec r p q A t u

  zeroₘ     : 𝟘ᶜ ▸[ m ] zero
  sucₘ      : γ ▸[ m ] t
            → γ ▸[ m ] suc t

  natrecₘ   : ∀ {G z s n}
            → γ ▸[ m ] z
            → δ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · r ▸[ m ] s
            → η ▸[ m ] n
            → θ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] G
            → (γ ∧ᶜ η) ⊛ᶜ (δ +ᶜ p ·ᶜ η) ▷ r ▸[ m ] natrec p q r G z s n

  Emptyrecₘ : γ ▸[ m ᵐ· p ] t
            → δ ▸[ 𝟘ᵐ? ] A
            → p ·ᶜ γ ▸[ m ] Emptyrec p A t

  starₘ     : 𝟘ᶜ ▸[ m ] star

  sub       : γ ▸[ m ] t
            → δ ≤ᶜ γ
            → δ ▸[ m ] t



-- Modality context inference

infix 50 ⌈_⌉

mutual
  ⌈_⌉ : Term n → Mode → Conₘ n
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
  ⌈ Emptyrec p A e ⌉ m = p ·ᶜ ⌈ e ⌉ (m ᵐ· p)
