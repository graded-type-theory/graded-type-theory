{-# OPTIONS --without-K --safe #-}

open import Tools.Level
open import Tools.Relation
open import Definition.Modality

module Definition.Modality.Usage {a ℓ}
  {M′ : Setoid a ℓ} (𝕄 : Modality M′)
  where

open Modality 𝕄
open Setoid M′ renaming (Carrier to M)

open import Definition.Modality.Context 𝕄
open import Definition.Untyped M hiding (_∙_)

open import Tools.Fin
open import Tools.Nat
import Tools.PropositionalEquality as PE

infix 10 _▸_

private
  variable
    n : Nat
    p q r : M
    γ δ γ′ η : Conₘ n
    A F : Term n
    G : Term (1+ n)
    t u : Term n
    x : Fin n
    m : SigmaMode

-- Well-usage of variables
data _◂_∈_  : (x : Fin n) (p : M) (γ : Conₘ n) → Set a where
  here  :                       x0 ◂ p ∈ γ ∙ p
  there : (h : x ◂ p ∈ γ) → (x +1) ◂ p ∈ γ ∙ q


-- Well-usage of terms
data _▸_ {n : Nat} : (γ : Conₘ n) → Term n → Set (a ⊔ ℓ) where
  Uₘ        : 𝟘ᶜ ▸ U
  ℕₘ        : 𝟘ᶜ ▸ ℕ
  Emptyₘ    : 𝟘ᶜ ▸ Empty
  Unitₘ     : 𝟘ᶜ ▸ Unit

  Πₘ        : γ ▸ F
            → δ ∙ q ▸ G
            → γ +ᶜ δ ▸ Π p , q ▷ F ▹ G

  Σₘ        : γ ▸ F
            → δ ∙ q ▸ G
            → γ +ᶜ δ ▸ Σ⟨ m ⟩ q ▷ F ▹ G

  var       : (𝟘ᶜ , x ≔ 𝟙) ▸ var x

  lamₘ      : ∀ {t}
            → γ ∙ p ▸ t
            → γ ▸ lam p t

  _∘ₘ_      : γ ▸ t
            → δ ▸ u
            → γ +ᶜ p ·ᶜ δ ▸ t ∘ p ▷ u

  prodᵣₘ    : γ ▸ t
            → δ ▸ u
            → γ′ PE.≡ (γ +ᶜ δ)
            → γ′ ▸ prodᵣ t u

  prodₚₘ   : γ ▸ t
           → γ ▸ u
           → γ ▸ prodₚ t u

  fstₘ      : γ ▸ t
            → γ ▸ fst t

  sndₘ      : γ ▸ t
            → γ ▸ snd t

  prodrecₘ  : γ ▸ t
            → δ ∙ p ∙ p ▸ u
            → Prodrec p
            → p ·ᶜ γ +ᶜ δ ▸ prodrec p A t u

  zeroₘ     : 𝟘ᶜ ▸ zero
  sucₘ      : γ ▸ t
            → γ ▸ suc t

  natrecₘ   : ∀ {G z s n}
            → γ ▸ z
            → δ ∙ p ∙ r ▸ s
            → η ▸ n
            → (γ ∧ᶜ η) ⊛ᶜ (δ +ᶜ p ·ᶜ η) ▷ r ▸ natrec p r G z s n

  Emptyrecₘ : γ ▸ t
            → p ·ᶜ γ ▸ Emptyrec p A t

  starₘ     : 𝟘ᶜ ▸ star

  sub       : γ ▸ t
            → δ ≤ᶜ γ
            → δ ▸ t



-- Modality context inference

infix 50 ⌈_⌉

mutual
  ⌈_⌉ : Term n → Conₘ n
  ⌈ var x ⌉ = 𝟘ᶜ , x ≔ 𝟙
  ⌈ gen k ts ⌉ = gen-usage k ts

  gen-usage : ∀ {n bs} (k : Kind bs) → (ts : GenTs Term n bs) → Conₘ n
  gen-usage Ukind []                         = 𝟘ᶜ
  gen-usage (Pikind p q) (F ∷ G ∷ [])        = ⌈ F ⌉ +ᶜ tailₘ ⌈ G ⌉
  gen-usage (Lamkind p) (t ∷ [])             = tailₘ ⌈ t ⌉
  gen-usage (Appkind p) (t ∷ u ∷ [])         = ⌈ t ⌉ +ᶜ p ·ᶜ ⌈ u ⌉
  gen-usage (Sigmakind q m) (F ∷ G ∷ [])     = ⌈ F ⌉ +ᶜ tailₘ ⌈ G ⌉
  gen-usage (Prodkind Σᵣ) (t ∷ u ∷ [])       = ⌈ t ⌉ +ᶜ ⌈ u ⌉
  gen-usage (Prodkind Σₚ) (t ∷ u ∷ [])       = ⌈ t ⌉ ∧ᶜ ⌈ u ⌉
  gen-usage Fstkind (t ∷ [])                 = ⌈ t ⌉
  gen-usage Sndkind (t ∷ [])                 = ⌈ t ⌉
  gen-usage (Prodreckind p) (A ∷ t ∷ u ∷ []) = p ·ᶜ ⌈ t ⌉ +ᶜ tailₘ (tailₘ ⌈ u ⌉)
  gen-usage Natkind  []                      = 𝟘ᶜ
  gen-usage Zerokind []                      = 𝟘ᶜ
  gen-usage Suckind (t ∷ [])                 = ⌈ t ⌉
  gen-usage Unitkind  []                     = 𝟘ᶜ
  gen-usage Starkind  []                     = 𝟘ᶜ
  gen-usage Emptykind []                     = 𝟘ᶜ
  gen-usage (Emptyreckind p) (A ∷ e ∷ [])    = p ·ᶜ ⌈ e ⌉
  gen-usage (Natreckind p r) (G ∷ z ∷ s ∷ n ∷ []) =
    let γ  = ⌈ z ⌉
        δ′ = ⌈ s ⌉
        η  = ⌈ n ⌉
        δ  = tailₘ (tailₘ δ′)
    in  (γ ∧ᶜ η) ⊛ᶜ (δ +ᶜ p ·ᶜ η) ▷ r
