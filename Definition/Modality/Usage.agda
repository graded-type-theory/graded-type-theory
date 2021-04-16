{-# OPTIONS --without-K --safe #-}

open import Tools.Relation
open import Definition.Modality

module Definition.Modality.Usage
  {M : Set} {_≈_ : Rel M _}
  (𝕄 : Modality M _≈_)
  where

open import Definition.Modality.Context 𝕄
open import Definition.Untyped M _≈_ hiding (_∙_)

open import Tools.Fin
open import Tools.Nat
import Tools.PropositionalEquality as PE

open Modality 𝕄

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

-- Well-usage of variables
data _◂_∈_  : (x : Fin n) (p : M) (γ : Conₘ n) → Set where
  here  :                       x0 ◂ p ∈ γ ∙ p
  there : (h : x ◂ p ∈ γ) → (x +1) ◂ p ∈ γ ∙ q


-- Well-usage of terms
data _▸_ {n : Nat} : (γ : Conₘ n) → Term n → Set where
  Uₘ        : 𝟘ᶜ ▸ U
  ℕₘ        : 𝟘ᶜ ▸ ℕ
  Emptyₘ    : 𝟘ᶜ ▸ Empty
  Unitₘ     : 𝟘ᶜ ▸ Unit

  Πₘ        : γ ▸ F
            → δ ∙ q ▸ G
            → γ +ᶜ δ ▸ Π p , q ▷ F ▹ G

  Σₘ        : γ ▸ F
            → δ ∙ q ▸ G
            → γ +ᶜ δ ▸ Σ q ▷ F ▹ G

  var       : (𝟘ᶜ , x ≔ 𝟙) ▸ var x

  lamₘ      : ∀ {t}
            → γ ∙ p ▸ t
            → γ ▸ lam p t

  _∘ₘ_      : γ ▸ t
            → δ ▸ u
            → γ +ᶜ p ·ᶜ δ ▸ t ∘ p ▷ u

  prodₘ     : γ ▸ t
            → δ ▸ u
            → γ′ PE.≡ (γ +ᶜ δ)
            → γ′ ▸ prod t u

  fstₘ      : 𝟘ᶜ ▸ t
            → 𝟘ᶜ ▸ fst t

  sndₘ      : 𝟘ᶜ ▸ t
            → 𝟘ᶜ ▸ snd t

  prodrecₘ  : γ ▸ t
            → δ ∙ p ∙ p ▸ u
            → p ·ᶜ γ +ᶜ δ ▸ prodrec p G t u

  zeroₘ     : 𝟘ᶜ ▸ zero
  sucₘ      : γ ▸ t
            → γ ▸ suc t

  natrecₘ   : ∀ {G z s n}
            → γ ▸ z
            → δ ∙ p ∙ r ▸ s
            → η ▸ n
            {-
            If X ▸ natrec p r G z s n,
            need X ≤ γ and X ≤ δ + pη + rX for preservation
            -}
            -- → γ′ ≡ δ +ᶜ r ·ᶜ (γ ∧ᶜ γ′) +ᶜ p ·ᶜ η
            -- γ′ ≤ δ + pη + r(γ ∧ γ′)
            -- γ′ ≤ (δ + pη + rγ) ∧ (δ + pη + rγ′)
            -- a ≤ b + cd ∧ b + ca
            -- → γ ∧ᶜ γ′ ▸ natrec p r G z s n
            -- → γ ∧ᶜ (recᶜ (δ + pη + rγ) (δ + pη) r) ▸ natrec p r G z s n
            → γ ∧ᶜ nrᶜ (δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ γ) (δ +ᶜ p ·ᶜ η) r ▸ natrec p r G z s n

  Emptyrecₘ : γ ▸ t
            → γ ▸ Emptyrec p A t

  starₘ     : 𝟘ᶜ ▸ star

  sub       : γ ▸ t
            → δ ≤ᶜ γ
            → δ ▸ t

pattern prodₘ! x y = prodₘ x y PE.refl

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
  gen-usage (Sigmakind p) (F ∷ G ∷ [])       = ⌈ F ⌉ +ᶜ tailₘ ⌈ G ⌉
  gen-usage Prodkind (t ∷ u ∷ [])            = ⌈ t ⌉ +ᶜ ⌈ u ⌉
  gen-usage Fstkind (t ∷ [])                 = 𝟘ᶜ
  gen-usage Sndkind (t ∷ [])                 = 𝟘ᶜ
  gen-usage (Prodreckind p) (G ∷ t ∷ u ∷ []) = p ·ᶜ ⌈ t ⌉ +ᶜ tailₘ (tailₘ ⌈ u ⌉)
  gen-usage Natkind  []                      = 𝟘ᶜ
  gen-usage Zerokind []                      = 𝟘ᶜ
  gen-usage Suckind (t ∷ [])                 = ⌈ t ⌉
  gen-usage Unitkind  []                     = 𝟘ᶜ
  gen-usage Starkind  []                     = 𝟘ᶜ
  gen-usage Emptykind []                     = 𝟘ᶜ
  gen-usage (Emptyreckind p) (A ∷ e ∷ [])    = ⌈ e ⌉
  gen-usage (Natreckind p r) (G ∷ z ∷ s ∷ n ∷ []) =
    let γ  = ⌈ z ⌉
        δ  = tailₘ (tailₘ δ′)
        δ′ = ⌈ s ⌉
        r  = headₘ δ′
        η  = ⌈ n ⌉
        p  = headₘ (tailₘ δ′)
    in  γ ∧ᶜ (nrᶜ (δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ γ) (δ +ᶜ p ·ᶜ η) r)
