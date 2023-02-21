open import Tools.Level
open import Tools.Relation
open import Definition.Modality

module Definition.Modality.Usage {a ℓ}
  {M′ : Setoid a ℓ} (𝕄 : Modality M′)
  where

open Modality 𝕄
open Setoid M′ renaming (Carrier to M)

open import Definition.Modality.Context 𝕄
open import Definition.Mode 𝕄
open import Definition.Untyped M hiding (_∙_)

open import Tools.Fin
open import Tools.Nat
import Tools.PropositionalEquality as PE

infix 10 _▸[_]_

private
  variable
    n : Nat
    p q r : M
    γ δ γ′ η : Conₘ n
    A F : Term n
    G : Term (1+ n)
    t u : Term n
    x : Fin n
    m : Mode
    s : SigmaMode

-- Well-usage of variables
data _◂_∈_  : (x : Fin n) (p : M) (γ : Conₘ n) → Set a where
  here  :                       x0 ◂ p ∈ γ ∙ p
  there : (h : x ◂ p ∈ γ) → (x +1) ◂ p ∈ γ ∙ q

-- Well-usage relation for terms.
--
-- The definition is partly based on Bob Atkey's "Syntax and Semantics
-- of Quantitative Type Theory".
data _▸[_]_ {n : Nat} : (γ : Conₘ n) → Mode → Term n → Set (a ⊔ ℓ) where
  Uₘ        : 𝟘ᶜ ▸[ m ] U
  ℕₘ        : 𝟘ᶜ ▸[ m ] ℕ
  Emptyₘ    : 𝟘ᶜ ▸[ m ] Empty
  Unitₘ     : 𝟘ᶜ ▸[ m ] Unit

  Πₘ        : γ ▸[ m ᵐ· p ] F
            → δ ∙ ⌜ m ⌝ · q ▸[ m ] G
            → γ +ᶜ δ ▸[ m ] Π p , q ▷ F ▹ G

  Σₘ        : γ ▸[ m ] F
            → δ ∙ ⌜ m ⌝ · q ▸[ m ] G
            → γ +ᶜ δ ▸[ m ] Σ⟨ s ⟩ q ▷ F ▹ G

  var       : (𝟘ᶜ , x ≔ ⌜ m ⌝) ▸[ m ] var x

  lamₘ      : ∀ {t}
            → γ ∙ ⌜ m ⌝ · p ▸[ m ] t
            → γ ▸[ m ] lam p t

  _∘ₘ_      : γ ▸[ m ] t
            → δ ▸[ m ᵐ· p ] u
            → γ +ᶜ p ·ᶜ δ ▸[ m ] t ∘⟨ p ⟩ u

  prodᵣₘ    : γ ▸[ m ] t
            → δ ▸[ m ] u
            → γ′ PE.≡ γ +ᶜ δ
            → γ′ ▸[ m ] prodᵣ t u

  prodₚₘ   : γ ▸[ m ] t
           → γ ▸[ m ] u
           → γ ▸[ m ] prodₚ t u

  fstₘ      : γ ▸[ m ] t
            → γ ▸[ m ] fst t

  sndₘ      : γ ▸[ m ] t
            → γ ▸[ m ] snd t

  prodrecₘ  : γ ▸[ m ᵐ· p ] t
            → δ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · p ▸[ m ] u
            → Prodrec p
            → p ·ᶜ γ +ᶜ δ ▸[ m ] prodrec p A t u

  zeroₘ     : 𝟘ᶜ ▸[ m ] zero
  sucₘ      : γ ▸[ m ] t
            → γ ▸[ m ] suc t

  natrecₘ   : ∀ {G z s n}
            → γ ▸[ m ] z
            → δ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · r ▸[ m ] s
            → η ▸[ m ] n
            → (γ ∧ᶜ η) ⊛ᶜ (δ +ᶜ p ·ᶜ η) ▷ r ▸[ m ] natrec p r G z s n

  Emptyrecₘ : γ ▸[ m ᵐ· p ] t
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
  ⌈ Π p , q ▷ F ▹ G ⌉ m = ⌈ F ⌉ (m ᵐ· p) +ᶜ tailₘ (⌈ G ⌉ m)
  ⌈ lam p t ⌉ m = tailₘ (⌈ t ⌉ m)
  ⌈ t ∘⟨ p ⟩ u ⌉ m = ⌈ t ⌉ m +ᶜ p ·ᶜ ⌈ u ⌉ (m ᵐ· p)
  ⌈ Σ q ▷ F ▹ G ⌉ m = ⌈ F ⌉ m +ᶜ tailₘ (⌈ G ⌉ m)
  ⌈ prod Σᵣ t u ⌉ m = ⌈ t ⌉ m +ᶜ ⌈ u ⌉ m
  ⌈ prod Σₚ t u ⌉ m = ⌈ t ⌉ m ∧ᶜ ⌈ u ⌉ m
  ⌈ fst t ⌉ m = ⌈ t ⌉ m
  ⌈ snd t ⌉ m = ⌈ t ⌉ m
  ⌈ prodrec p A t u ⌉ m = p ·ᶜ ⌈ t ⌉ (m ᵐ· p) +ᶜ tailₘ (tailₘ (⌈ u ⌉ m))
  ⌈ ℕ ⌉ _ = 𝟘ᶜ
  ⌈ zero ⌉ _ = 𝟘ᶜ
  ⌈ suc t ⌉ m = ⌈ t ⌉ m
  ⌈ natrec p r A z s n ⌉ m =
    let γ  = ⌈ z ⌉ m
        δ′ = ⌈ s ⌉ m
        η  = ⌈ n ⌉ m
        δ  = tailₘ (tailₘ δ′)
    in  (γ ∧ᶜ η) ⊛ᶜ (δ +ᶜ p ·ᶜ η) ▷ r
  ⌈ Unit ⌉ _ = 𝟘ᶜ
  ⌈ star ⌉ _ = 𝟘ᶜ
  ⌈ Empty ⌉ _ = 𝟘ᶜ
  ⌈ Emptyrec p A e ⌉ m = p ·ᶜ ⌈ e ⌉ (m ᵐ· p)
