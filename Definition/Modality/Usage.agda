module Definition.Modality.Usage where

open import Definition.Modality
open import Definition.Modality.Context
open import Definition.Modality.Context.Properties
open import Definition.Untyped

open import Tools.Fin
open import Tools.Nat
open import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    M : Set
    𝕄 : Modality M
    p q r : M
    γ δ : ConM 𝕄 n
    A F : Term M n
    G : Term M (1+ n)
    t u : Term M n
    x : Fin n

-- Well-usage of variables
data _◂_∈_ : (x : Fin n) (p : M) (γ : ConM 𝕄 n) → Set₁ where
  here  :                       x0 ◂ p ∈ γ ∙ p
  there : (h : x ◂ p ∈ γ) → (x +1) ◂ p ∈ γ ∙ q

-- Well-usage of terms
data _▸_ {n : Nat} {𝕄 : Modality M} : (γ : ConM 𝕄 n) → Term M n → Set₁ where
  Uₘ        : 𝟘ᶜ ▸ U
  ℕₘ        : 𝟘ᶜ ▸ ℕ
  Emptyₘ    : 𝟘ᶜ ▸ Empty
  Unitₘ     : 𝟘ᶜ ▸ Unit

  Πₘ        : γ ▸ F
            → (δ ∙ q) ▸ G
            → (γ +ᶜ δ) ▸ Π p , q ▷ F ▹ G

  Σₘ        : γ ▸ F
            → (δ ∙ p) ▸ G
            → (γ +ᶜ δ) ▸ Σ p ▷ F ▹ G

  var       : (𝟘ᶜ , x ≔ (Modality.𝟙 𝕄)) ▸ var x

  lamₘ      : ∀ {t}
            → (γ ∙ p) ▸ t
            → γ ▸ lam p t
            
  _∘ₘ_      : γ ▸ t
            → δ ▸ u
            → (γ +ᶜ p ·ᶜ δ) ▸ (p ▷ t ∘ u)

  prodₘ     : γ ▸ t
            → δ ▸ u
            → (γ +ᶜ δ) ▸ prod t u
            
  fstₘ      : 𝟘ᶜ {𝕄 = 𝕄} ▸ t
            → 𝟘ᶜ ▸ fst t
            
  sndₘ      : 𝟘ᶜ {𝕄 = 𝕄} ▸ t
            → 𝟘ᶜ ▸ snd t
            
  prodrecₘ  : γ ▸ t
            → (δ ∙ p ∙ q) ▸ u
            → (γ +ᶜ δ) ▸ (prodrec p q t u)

  zeroₘ     : 𝟘ᶜ ▸ zero
  sucₘ      : γ ▸ t
            → γ ▸ suc t

  natrecₘ   : ∀ {G z s n}
            → γ ▸ z
            → γ ▸ (lam p (lam q s))
            → δ ▸ n
            → r ≡ (Modality._+_ 𝕄 (Modality.𝟙 𝕄) (Modality._·_ 𝕄 q r))
            → r ·ᶜ (γ +ᶜ p ·ᶜ δ) ▸ natrec G z (lam p (lam q s)) n

  Emptyrecₘ : γ ▸ t
            → γ ▸ (Emptyrec p A t)

  starₘ     : 𝟘ᶜ ▸ star

  sub       : γ ▸ t
            → δ ≤ᶜ γ
            → δ ▸ t
            
infix 50 ⌊_⌋

postulate
  min : M
  isMin : (p : M) → Modality._≤_ 𝕄 p min → p ≡ min

mutual
  ⌊_⌋ : {𝕄 : Modality M} → Term M n → ConM 𝕄 n
  ⌊_⌋ {𝕄 = 𝕄} (var x) = 𝟘ᶜ , x ≔ (Modality.𝟙 𝕄)
  ⌊ gen k ts ⌋ = gen-usage k ts

  gen-usage : ∀ {n bs} {𝕄 : Modality M} (k : Kind M bs) → (ts : GenTs (Term M) n bs) → ConM 𝕄 n
  gen-usage Ukind []                        = 𝟘ᶜ
  gen-usage (Pikind p q) (F ∷ G ∷ [])       = ⌊ F ⌋ +ᶜ (tailₘ ⌊ G ⌋)
  gen-usage (Lamkind p) (t ∷ [])            = tailₘ ⌊ t ⌋
  gen-usage (Appkind p) (t ∷ u ∷ [])        = ⌊ t ⌋ +ᶜ p ·ᶜ ⌊ u ⌋
  gen-usage (Sigmakind p) (F ∷ G ∷ [])      = ⌊ F ⌋ +ᶜ (tailₘ ⌊ G ⌋)
  gen-usage Prodkind (t ∷ u ∷ [])           = ⌊ t ⌋ +ᶜ ⌊ u ⌋
  gen-usage Fstkind (t ∷ [])                = ⌊ t ⌋
  gen-usage Sndkind (t ∷ [])                = ⌊ t ⌋
  gen-usage (Prodreckind p q) (t ∷ u ∷ [])  = ⌊ t ⌋ +ᶜ tailₘ (tailₘ ⌊ u ⌋)
  gen-usage Natkind  []                     = 𝟘ᶜ
  gen-usage Zerokind []                     = 𝟘ᶜ
  gen-usage Suckind (t ∷ [])                = ⌊ t ⌋
  gen-usage Unitkind  []                    = 𝟘ᶜ
  gen-usage Starkind  []                    = 𝟘ᶜ
  gen-usage Emptykind []                    = 𝟘ᶜ
  gen-usage (Emptyreckind p) (A ∷ e ∷ [])   = ⌊ e ⌋
  gen-usage {𝕄 = 𝕄} Natreckind (G ∷ z ∷ s ∷ n ∷ []) = min ·ᶜ (⌊ s ⌋ +ᶜ min ·ᶜ ⌊ n ⌋)

{-

usage-correctness : γ ▸ t → γ ≤ᶜ ⌊ t ⌋
usage-correctness Uₘ = ≤ᶜ-reflexive
usage-correctness ℕₘ = ≤ᶜ-reflexive
usage-correctness Emptyₘ = ≤ᶜ-reflexive
usage-correctness Unitₘ = ≤ᶜ-reflexive
usage-correctness (Πₘ {δ = δ} {q} {G₁} F G) = +ᶜ-monotone₂ (usage-correctness F)
                         (PE.subst (δ ≡_) (tail-linear∧ {γ = δ ∙ q} {⌊ G₁ ⌋})
                                          (cong tailₘ (usage-correctness G)))
usage-correctness (Σₘ {δ = δ} {q} {G₁} F G) = +ᶜ-monotone₂ (usage-correctness F)
                         (PE.subst (δ ≡_) (tail-linear∧ {γ = δ ∙ q} {⌊ G₁ ⌋})
                                          (cong tailₘ (usage-correctness G)))
usage-correctness var = ≤ᶜ-reflexive
usage-correctness {γ = γ} (lamₘ {p = p} {t₁} t) = PE.subst (γ ≡_)
                                        (tail-linear∧ {γ = γ ∙ p} {⌊ t₁ ⌋})
                                        (cong tailₘ (usage-correctness t))
usage-correctness (t ∘ₘ u) = +ᶜ-monotone₂ (usage-correctness t) (·ᶜ-monotone (usage-correctness u))
usage-correctness (prodₘ t u) = +ᶜ-monotone₂ (usage-correctness t) (usage-correctness u)
usage-correctness (fstₘ t) = usage-correctness t
usage-correctness (sndₘ t) = usage-correctness t
usage-correctness (prodrecₘ {γ} {δ = δ} {p} {u = u₁} t u) = +ᶜ-monotone₂
  (usage-correctness t)
  (PE.subst (δ ≡_)
    (subst₂ _≡_
      (sym (tail-linear∧ {γ = δ ∙ p} {⌊ {!u₁!} ⌋}))
      (tail-linear∧ {γ = δ ∙ p} {⌊ {!!} ⌋})
      (tail-linear∧ {γ = δ ∙ p} {{!!}})
    )
    (cong tailₘ (cong tailₘ (usage-correctness u)))
  )
-- (PE.subst {!!} {!!} {!!})
-- {!cong tailₘ (cong tailₘ (usage-correctness u))!}
usage-correctness zeroₘ = ≤ᶜ-reflexive
usage-correctness (sucₘ t) = usage-correctness t
usage-correctness (natrecₘ x x₁ x₂ x₃) = {!!}
usage-correctness (Emptyrecₘ e) = usage-correctness e
usage-correctness starₘ = ≤ᶜ-reflexive
usage-correctness (sub t x) = ≤ᶜ-transitive x (usage-correctness t)
-}
