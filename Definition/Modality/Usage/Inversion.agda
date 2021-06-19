{-# OPTIONS --without-K --safe #-}

open import Tools.Level
open import Tools.Relation
open import Definition.Modality

module Definition.Modality.Usage.Inversion
  {M : Set} {_≈_ : Rel M ℓ₀}
  (𝕄 : Modality M _≈_)
  where

open import Definition.Modality.Context 𝕄
open import Definition.Modality.Context.Properties 𝕄
open import Definition.Modality.Usage 𝕄
open import Definition.Untyped M hiding (_∙_)

open import Tools.Nat
open import Tools.PropositionalEquality

open Modality 𝕄

private
  variable
    n : Nat
    γ γ′ : Conₘ n
    p q r : M
    A F t u z n' : Term n
    G : Term (1+ n)
    s : Term (1+ (1+ n))

-- Inversion lemmata for  γ ▸ t

-- If γ ▸ U then γ ≤ᶜ 𝟘ᶜ

inv-usage-U : γ ▸ U → γ ≤ᶜ 𝟘ᶜ
inv-usage-U Uₘ = ≤ᶜ-refl
inv-usage-U (sub γ▸U γ≤δ) = ≤ᶜ-trans γ≤δ (inv-usage-U γ▸U)

-- If γ ▸ ℕ then γ ≤ᶜ 𝟘ᶜ

inv-usage-ℕ : γ ▸ ℕ → γ ≤ᶜ 𝟘ᶜ
inv-usage-ℕ ℕₘ = ≤ᶜ-refl
inv-usage-ℕ (sub γ▸ℕ γ≤δ) = ≤ᶜ-trans γ≤δ (inv-usage-ℕ γ▸ℕ)

-- If γ ▸ Empty then γ ≤ᶜ 𝟘ᶜ

inv-usage-Empty : γ ▸ Empty → γ ≤ᶜ 𝟘ᶜ
inv-usage-Empty Emptyₘ = ≤ᶜ-refl
inv-usage-Empty (sub γ▸⊥ γ≤δ) = ≤ᶜ-trans γ≤δ (inv-usage-Empty γ▸⊥)

-- If γ ▸ Unit then γ ≤ᶜ 𝟘ᶜ

inv-usage-Unit : γ ▸ Unit → γ ≤ᶜ 𝟘ᶜ
inv-usage-Unit Unitₘ = ≤ᶜ-refl
inv-usage-Unit (sub γ▸⊤ γ≤δ) = ≤ᶜ-trans γ≤δ (inv-usage-Unit γ▸⊤)


record InvUsageΠΣ {n} (γ : Conₘ n) (q : M)
                  (F : Term n) (G : Term (1+ n)) : Set where
  constructor invUsageΠΣ
  field
    {δ η} : Conₘ n
    δ▸F   : δ ▸ F
    η▸G   : η ∙ q ▸ G
    γ≤δ+η : γ ≤ᶜ δ +ᶜ η

-- If γ ▸ Π p , q ▷ F ▹ G then δ ▸ F, η ∙ q ▸ G and γ ≤ᶜ δ +ᶜ η

inv-usage-Π : γ ▸ Π p , q ▷ F ▹ G → InvUsageΠΣ γ q F G
inv-usage-Π (Πₘ γ▸F δ▸G) = invUsageΠΣ γ▸F δ▸G ≤ᶜ-refl
inv-usage-Π (sub γ▸Π γ≤γ′) with inv-usage-Π γ▸Π
... | invUsageΠΣ δ▸F η▸G γ′≤δ+η = invUsageΠΣ δ▸F η▸G (≤ᶜ-trans γ≤γ′ γ′≤δ+η)

-- If γ ▸ Σ p , q ▷ F ▹ G then δ ▸ F, η ∙ q ▸ G and γ ≤ᶜ δ +ᶜ η

inv-usage-Σ : γ ▸ Σ q ▷ F ▹ G → InvUsageΠΣ γ q F G
inv-usage-Σ (Σₘ γ▸F δ▸G) = invUsageΠΣ γ▸F δ▸G ≤ᶜ-refl
inv-usage-Σ (sub γ▸Σ γ≤γ′) with inv-usage-Σ γ▸Σ
... | invUsageΠΣ δ▸F η▸G γ′≤δ+η = invUsageΠΣ δ▸F η▸G (≤ᶜ-trans γ≤γ′ γ′≤δ+η)

-- If γ ▸ var x then γ ≤ᶜ (𝟘ᶜ , x ≔ 𝟙)

inv-usage-var : ∀ {x} {γ : Conₘ n}
              → γ ▸ var x → γ ≤ᶜ (𝟘ᶜ , x ≔ 𝟙)
inv-usage-var var = ≤ᶜ-refl
inv-usage-var (sub γ▸x γ≤γ′) with inv-usage-var γ▸x
... | γ′≤δ = ≤ᶜ-trans γ≤γ′ γ′≤δ


record InvUsageLam {n} (γ : Conₘ n) (p : M) (t : Term (1+ n)) : Set where
  constructor invUsageLam
  field
    {δ} : Conₘ n
    δ▸t : δ ∙ p ▸ t
    γ≤δ : γ ≤ᶜ δ

-- If γ ▸ λ p t then δ ∙ p ▸ t and γ ≤ᶜ δ

inv-usage-lam : γ ▸ lam p t → InvUsageLam γ p t
inv-usage-lam (lamₘ γ▸λpt) = invUsageLam γ▸λpt ≤ᶜ-refl
inv-usage-lam (sub γ′▸λpt γ≤γ′) with inv-usage-lam γ′▸λpt
... | invUsageLam δ▸t γ′≤δ = invUsageLam δ▸t (≤ᶜ-trans γ≤γ′ γ′≤δ)


record InvUsageApp {n} (γ : Conₘ n) (t : Term n) (p : M) (u : Term n) : Set where
  constructor invUsageApp
  field
    {δ η}  : Conₘ n
    δ▸t    : δ ▸ t
    η▸u    : η ▸ u
    γ≤δ+pη : γ ≤ᶜ (δ +ᶜ p ·ᶜ η)

-- If γ ▸ t ∘ p ▷ u then δ ▸ t, η ▸ u and γ ≤ᶜ δ +ᶜ p ·ᶜ η

inv-usage-app : γ′ ▸ (t ∘ p ▷ u) → InvUsageApp γ′ t p u
inv-usage-app (γ▸t ∘ₘ δ▸u) = invUsageApp γ▸t δ▸u ≤ᶜ-refl
inv-usage-app (sub γ▸t∘p▷u γ′≤γ) with inv-usage-app γ▸t∘p▷u
... | invUsageApp δ▸t η▸u γ≤δ+pη = invUsageApp δ▸t η▸u (≤ᶜ-trans γ′≤γ γ≤δ+pη)


record InvUsageProd {n} (γ′ : Conₘ n) (t u : Term n) : Set where
  constructor invUsageProd
  field
    {δ η γ″} : Conₘ n
    δ▸t     : δ ▸ t
    η▸u     : η ▸ u
    γ″=δ+η  : γ″ ≡ δ +ᶜ η
    γ′≤γ″   : γ′ ≤ᶜ γ″

-- If γ ▸ prod t u then δ ▸ t, η ▸ u and γ ≤ᶜ δ +ᶜ η

inv-usage-prod : γ ▸ prod t u → InvUsageProd γ t u
inv-usage-prod (prodₘ! γ▸t δ▸u) = invUsageProd γ▸t δ▸u refl ≤ᶜ-refl
inv-usage-prod (sub γ▸tu γ≤γ′) with inv-usage-prod γ▸tu
... | invUsageProd δ▸t η▸u γ″=δ+η γ′≤γ″ = invUsageProd δ▸t η▸u γ″=δ+η
  (≤ᶜ-trans γ≤γ′ γ′≤γ″)


record InvUsageProj {n} (γ : Conₘ n) (t : Term n) : Set where
  constructor invUsageProj
  field
    𝟘▸t : 𝟘ᶜ ▸ t
    γ≤𝟘 : γ ≤ᶜ 𝟘ᶜ

-- If γ ▸ fst t then 𝟘ᶜ ▸ t and γ ≤ᶜ 𝟘ᶜ

inv-usage-fst : γ ▸ fst t → InvUsageProj γ t
inv-usage-fst (fstₘ 𝟘▸t) = invUsageProj 𝟘▸t ≤ᶜ-refl
inv-usage-fst (sub γ▸t₁ γ≤γ′) with inv-usage-fst γ▸t₁
... | invUsageProj 𝟘▸t γ′≤𝟘 = invUsageProj 𝟘▸t (≤ᶜ-trans γ≤γ′ γ′≤𝟘)

-- If γ ▸ snd t then 𝟘ᶜ ▸ t and γ ≤ᶜ 𝟘ᶜ

inv-usage-snd : γ ▸ snd t → InvUsageProj γ t
inv-usage-snd (sndₘ 𝟘▸t) = invUsageProj 𝟘▸t ≤ᶜ-refl
inv-usage-snd (sub γ▸t₂ γ≤γ′) with inv-usage-snd γ▸t₂
... | invUsageProj 𝟘▸t γ′≤𝟘 = invUsageProj 𝟘▸t (≤ᶜ-trans γ≤γ′ γ′≤𝟘)


record InvUsageProdrec {n} (γ : Conₘ n) (p : M) (t : Term n)
                       (u : Term (1+ (1+ n))) : Set where
  constructor invUsageProdrec
  field
    {δ η}  : Conₘ n
    δ▸t    : δ ▸ t
    η▸u    : η ∙ p ∙ p ▸ u
    γ≤pδ+η : γ ≤ᶜ p ·ᶜ δ +ᶜ η

-- If γ ▸ prodrec p A t u then δ ▸ t, η ∙ p ∙ p ▸ u and γ ≤ᶜ p ·ᶜ δ +ᶜ η

inv-usage-prodrec : γ ▸ prodrec p G t u → InvUsageProdrec γ p t u
inv-usage-prodrec (prodrecₘ δ▸t η▸u) = invUsageProdrec δ▸t η▸u ≤ᶜ-refl
inv-usage-prodrec (sub γ▸x γ≤γ′) with inv-usage-prodrec γ▸x
... | invUsageProdrec δ▸t η▸u γ′≤pδ+η = invUsageProdrec δ▸t η▸u (≤ᶜ-trans γ≤γ′ γ′≤pδ+η)

-- If γ ▸ zero then γ ≤ᶜ 𝟘ᶜ

inv-usage-zero : γ ▸ zero → γ ≤ᶜ 𝟘ᶜ
inv-usage-zero zeroₘ = ≤ᶜ-refl
inv-usage-zero (sub  δ▸zero γ≤δ) = ≤ᶜ-trans γ≤δ (inv-usage-zero δ▸zero)


record InvUsageSuc {n} (γ : Conₘ n) (t : Term n) : Set where
  constructor invUsageSuc
  field
    {δ} : Conₘ n
    δ▸t : δ ▸ t
    γ≤δ : γ ≤ᶜ δ

-- If γ ▸ suc t then δ ▸ t and γ ≤ᶜ δ

inv-usage-suc : γ ▸ suc t → InvUsageSuc γ t
inv-usage-suc (sucₘ γ▸t) = invUsageSuc γ▸t ≤ᶜ-refl
inv-usage-suc (sub γ▸st γ≤γ′) with inv-usage-suc γ▸st
... | invUsageSuc δ▸t γ′≤δ = invUsageSuc δ▸t (≤ᶜ-trans γ≤γ′ γ′≤δ)


record InvUsageNatrec {m} (γ : Conₘ m) (p r : M) (z : Term m)
                      (s : Term (1+ (1+ m))) (n : Term m) : Set where
  constructor invUsageNatrec
  field
    {δ η θ} : Conₘ m
    δ▸z  : δ ▸ z
    η▸s  : η ∙ p ∙ r ▸ s
    θ▸n  : θ ▸ n
    γ≤γ′ : γ ≤ᶜ nrᶜ (δ ∧ᶜ θ) (η +ᶜ p ·ᶜ θ) r

-- If γ ▸ natrec p r G z s n then δ ▸ z, δ ∙ r ∙ p ▸ s, η ▸ n and γ ≤ᶜ r* ·ᶜ (δ +ᶜ p ·ᶜ η)

inv-usage-natrec : {p r : M} → γ ▸ natrec p r G z s n' → InvUsageNatrec γ p r z s n'
inv-usage-natrec (natrecₘ δ▸z δ▸s η▸n) = invUsageNatrec δ▸z δ▸s η▸n ≤ᶜ-refl
inv-usage-natrec (sub γ▸natrec γ≤γ′) with inv-usage-natrec γ▸natrec
... | invUsageNatrec δ▸z δ▸s η▸n γ′≤γ″ = invUsageNatrec δ▸z δ▸s η▸n (≤ᶜ-trans γ≤γ′ γ′≤γ″)


record InvUsageEmptyrec {n} (p : M) (γ : Conₘ n) (t : Term n) : Set where
  constructor invUsageEmptyrec
  field
    {δ} : Conₘ n
    δ▸t : δ ▸ t
    γ≤δ : γ ≤ᶜ p ·ᶜ δ

-- If γ ▸ Emptyrec p A t then δ ▸ t and γ ≤ᶜ δ

inv-usage-Emptyrec : γ ▸ Emptyrec p A t → InvUsageEmptyrec p γ t
inv-usage-Emptyrec (Emptyrecₘ δ▸t) = invUsageEmptyrec δ▸t ≤ᶜ-refl
inv-usage-Emptyrec (sub γ▸et γ≤γ′) with inv-usage-Emptyrec γ▸et
... | invUsageEmptyrec δ▸t γ′≤δ = invUsageEmptyrec δ▸t (≤ᶜ-trans γ≤γ′ γ′≤δ)

-- If γ ▸ star then γ ≤ᶜ 𝟘ᶜ

inv-usage-star : γ ▸ star → γ ≤ᶜ 𝟘ᶜ
inv-usage-star starₘ = ≤ᶜ-refl
inv-usage-star (sub  δ▸star γ≤δ) = ≤ᶜ-trans γ≤δ (inv-usage-star δ▸star)
