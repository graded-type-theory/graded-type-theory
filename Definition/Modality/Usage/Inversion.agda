{-# OPTIONS --without-K --safe #-}
module Definition.Modality.Usage.Inversion where

open import Definition.Modality
open import Definition.Modality.Context
open import Definition.Modality.Context.Properties
open import Definition.Modality.Usage
open import Definition.Untyped

open import Tools.Nat
open import Tools.PropositionalEquality

private
  variable
    n : Nat
    M : Set
    𝕄 : Modality M
    γ γ′ : Conₘ 𝕄 n
    p q r : M
    A F t u : Term M n
    G : Term M (1+ n)

-- Inversion lemmata for  γ ▸ t

-- If γ ▸ U then γ ≤ᶜ 𝟘ᶜ

inv-usage-U : γ ▸ U → γ ≤ᶜ 𝟘ᶜ
inv-usage-U Uₘ = ≤ᶜ-reflexive
inv-usage-U (sub γ▸U γ≤δ) = ≤ᶜ-transitive γ≤δ (inv-usage-U γ▸U)

-- If γ ▸ ℕ then γ ≤ᶜ 𝟘ᶜ

inv-usage-ℕ : γ ▸ ℕ → γ ≤ᶜ 𝟘ᶜ
inv-usage-ℕ ℕₘ = ≤ᶜ-reflexive
inv-usage-ℕ (sub γ▸ℕ γ≤δ) = ≤ᶜ-transitive γ≤δ (inv-usage-ℕ γ▸ℕ)

-- If γ ▸ Empty then γ ≤ᶜ 𝟘ᶜ

inv-usage-Empty : γ ▸ Empty → γ ≤ᶜ 𝟘ᶜ
inv-usage-Empty Emptyₘ = ≤ᶜ-reflexive
inv-usage-Empty (sub γ▸⊥ γ≤δ) = ≤ᶜ-transitive γ≤δ (inv-usage-Empty γ▸⊥)

-- If γ ▸ Unit then γ ≤ᶜ 𝟘ᶜ

inv-usage-Unit : γ ▸ Unit → γ ≤ᶜ 𝟘ᶜ
inv-usage-Unit Unitₘ = ≤ᶜ-reflexive
inv-usage-Unit (sub γ▸⊤ γ≤δ) = ≤ᶜ-transitive γ≤δ (inv-usage-Unit γ▸⊤)


record InvUsageΠΣ {n} {M} {𝕄 : Modality M} (γ : Conₘ 𝕄 n) (q : M)
                  (F : Term M n) (G : Term M (1+ n)) : Set where
  constructor invUsageΠΣ
  field
    {δ η} : Conₘ 𝕄 n
    δ▸F   : δ ▸ F
    η▸G   : η ∙ q ▸ G
    γ≤δ+η : γ ≤ᶜ δ +ᶜ η

-- If γ ▸ Π p , q ▷ F ▹ G then δ ▸ F, η ∙ q ▸ G and γ ≤ᶜ δ +ᶜ η

inv-usage-Π : γ ▸ Π p , q ▷ F ▹ G → InvUsageΠΣ γ q F G
inv-usage-Π (Πₘ γ▸F δ▸G) = invUsageΠΣ γ▸F δ▸G ≤ᶜ-reflexive
inv-usage-Π (sub γ▸Π γ≤γ′) with inv-usage-Π γ▸Π
... | invUsageΠΣ δ▸F η▸G γ′≤δ+η = invUsageΠΣ δ▸F η▸G (≤ᶜ-transitive γ≤γ′ γ′≤δ+η)

-- If γ ▸ Σ p , q ▷ F ▹ G then δ ▸ F, η ∙ q ▸ G and γ ≤ᶜ δ +ᶜ η

inv-usage-Σ : γ ▸ Σ q ▷ F ▹ G → InvUsageΠΣ γ q F G
inv-usage-Σ (Σₘ γ▸F δ▸G) = invUsageΠΣ γ▸F δ▸G ≤ᶜ-reflexive
inv-usage-Σ (sub γ▸Σ γ≤γ′) with inv-usage-Σ γ▸Σ
... | invUsageΠΣ δ▸F η▸G γ′≤δ+η = invUsageΠΣ δ▸F η▸G (≤ᶜ-transitive γ≤γ′ γ′≤δ+η)

-- If γ ▸ var x then γ ≤ᶜ (𝟘ᶜ , x ≔ 𝟙)

inv-usage-var : ∀ {x} {𝕄 : Modality M} {γ : Conₘ 𝕄 n}
              → γ ▸ var x → γ ≤ᶜ (𝟘ᶜ , x ≔ (Modality.𝟙 𝕄))
inv-usage-var var = ≤ᶜ-reflexive
inv-usage-var (sub γ▸x γ≤γ′) with inv-usage-var γ▸x
... | γ′≤δ = ≤ᶜ-transitive γ≤γ′ γ′≤δ


record InvUsageLam {n} {M} {𝕄 : Modality M} (γ : Conₘ 𝕄 n) (p : M) (t : Term M (1+ n)) : Set where
  constructor invUsageLam
  field
    {δ} : Conₘ 𝕄 n
    δ▸t : δ ∙ p ▸ t
    γ≤δ : γ ≤ᶜ δ

-- If γ ▸ λ p t then δ ∙ p ▸ t and γ ≤ᶜ δ

inv-usage-lam : γ ▸ lam p t → InvUsageLam γ p t
inv-usage-lam (lamₘ γ▸λpt) = invUsageLam γ▸λpt ≤ᶜ-reflexive
inv-usage-lam (sub γ′▸λpt γ≤γ′) with inv-usage-lam γ′▸λpt
... | invUsageLam δ▸t γ′≤δ = invUsageLam δ▸t (≤ᶜ-transitive γ≤γ′ γ′≤δ)


record InvUsageApp {n} {M} {𝕄 : Modality M} (γ : Conₘ 𝕄 n)
                   (t : Term M n) (p : M) (u : Term M n) : Set where
  constructor invUsageApp
  field
    {δ η}  : Conₘ 𝕄 n
    δ▸t    : δ ▸ t
    η▸u    : η ▸ u
    γ≤δ+pη : γ ≤ᶜ (δ +ᶜ p ·ᶜ η)

-- If γ ▸ t ∘ p ▷ u then δ ▸ t, η ▸ u and γ ≤ᶜ δ +ᶜ p ·ᶜ η

inv-usage-app : γ′ ▸ (t ∘ p ▷ u) → InvUsageApp γ′ t p u
inv-usage-app (γ▸t ∘ₘ δ▸u) = invUsageApp γ▸t δ▸u ≤ᶜ-reflexive
inv-usage-app (sub γ▸t∘p▷u γ′≤γ) with inv-usage-app γ▸t∘p▷u
... | invUsageApp δ▸t η▸u γ≤δ+pη = invUsageApp δ▸t η▸u (≤ᶜ-transitive γ′≤γ γ≤δ+pη)


record InvUsageProd {n} {M} {𝕄 : Modality M} (γ′ : Conₘ 𝕄 n)
                    (t u : Term M n) : Set where
  constructor invUsageProd
  field
    {δ η γ″} : Conₘ 𝕄 n
    δ▸t     : δ ▸ t
    η▸u     : η ▸ u
    γ″=δ+η  : γ″ ≡ δ +ᶜ η
    γ′≤γ″   : γ′ ≤ᶜ γ″

-- If γ ▸ prod t u then δ ▸ t, η ▸ u and γ ≤ᶜ δ +ᶜ η

inv-usage-prod : γ ▸ prod t u → InvUsageProd γ t u
inv-usage-prod (prodₘ! γ▸t δ▸u) = invUsageProd γ▸t δ▸u refl ≤ᶜ-reflexive
inv-usage-prod (sub γ▸tu γ≤γ′) with inv-usage-prod γ▸tu
... | invUsageProd δ▸t η▸u γ″=δ+η γ′≤γ″ = invUsageProd δ▸t η▸u γ″=δ+η
  (≤ᶜ-transitive γ≤γ′ γ′≤γ″)


record InvUsageProj {n} {M} {𝕄 : Modality M} (γ : Conₘ 𝕄 n) (t : Term M n) : Set where
  constructor invUsageProj
  field
    𝟘▸t : 𝟘ᶜ {𝕄 = 𝕄} ▸ t
    γ≤𝟘 : γ ≤ᶜ 𝟘ᶜ

-- If γ ▸ fst t then 𝟘ᶜ ▸ t and γ ≤ᶜ 𝟘ᶜ

inv-usage-fst : γ ▸ fst t → InvUsageProj γ t
inv-usage-fst (fstₘ 𝟘▸t) = invUsageProj 𝟘▸t ≤ᶜ-reflexive
inv-usage-fst (sub γ▸t₁ γ≤γ′) with inv-usage-fst γ▸t₁
... | invUsageProj 𝟘▸t γ′≤𝟘 = invUsageProj 𝟘▸t (≤ᶜ-transitive γ≤γ′ γ′≤𝟘)

-- If γ ▸ snd t then 𝟘ᶜ ▸ t and γ ≤ᶜ 𝟘ᶜ

inv-usage-snd : γ ▸ snd t → InvUsageProj γ t
inv-usage-snd (sndₘ 𝟘▸t) = invUsageProj 𝟘▸t ≤ᶜ-reflexive
inv-usage-snd (sub γ▸t₂ γ≤γ′) with inv-usage-snd γ▸t₂
... | invUsageProj 𝟘▸t γ′≤𝟘 = invUsageProj 𝟘▸t (≤ᶜ-transitive γ≤γ′ γ′≤𝟘)


record InvUsageProdrec {n} {M} {𝕄 : Modality M} (γ : Conₘ 𝕄 n) (p : M)
                       (t : Term M n) (u : Term M (1+ (1+ n))) : Set where
  constructor invUsageProdrec
  field
    {δ η}  : Conₘ 𝕄 n
    δ▸t    : δ ▸ t
    η▸u    : η ∙ p ∙ p ▸ u
    γ≤pδ+η : γ ≤ᶜ p ·ᶜ δ +ᶜ η

-- If γ ▸ prodrec p A t u then δ ▸ t, η ∙ p ∙ p ▸ u and γ ≤ᶜ p ·ᶜ δ +ᶜ η

inv-usage-prodrec : γ ▸ prodrec p G t u → InvUsageProdrec γ p t u
inv-usage-prodrec (prodrecₘ δ▸t η▸u) = invUsageProdrec δ▸t η▸u ≤ᶜ-reflexive
inv-usage-prodrec (sub γ▸x γ≤γ′) with inv-usage-prodrec γ▸x
... | invUsageProdrec δ▸t η▸u γ′≤pδ+η = invUsageProdrec δ▸t η▸u (≤ᶜ-transitive γ≤γ′ γ′≤pδ+η)

-- If γ ▸ zero then γ ≤ᶜ 𝟘ᶜ

inv-usage-zero : γ ▸ zero → γ ≤ᶜ 𝟘ᶜ
inv-usage-zero zeroₘ = ≤ᶜ-reflexive
inv-usage-zero (sub  δ▸zero γ≤δ) = ≤ᶜ-transitive γ≤δ (inv-usage-zero δ▸zero)


record InvUsageSuc {n} {M} {𝕄 : Modality M} (γ : Conₘ 𝕄 n) (t : Term M n) : Set where
  constructor invUsageSuc
  field
    {δ} : Conₘ 𝕄 n
    δ▸t : δ ▸ t
    γ≤δ : γ ≤ᶜ δ

-- If γ ▸ suc t then δ ▸ t and γ ≤ᶜ δ

inv-usage-suc : γ ▸ suc t → InvUsageSuc γ t
inv-usage-suc (sucₘ γ▸t) = invUsageSuc γ▸t ≤ᶜ-reflexive
inv-usage-suc (sub γ▸st γ≤γ′) with inv-usage-suc γ▸st
... | invUsageSuc δ▸t γ′≤δ = invUsageSuc δ▸t (≤ᶜ-transitive γ≤γ′ γ′≤δ)


record InvUsageNatrec {m} {M} {𝕄 : Modality M} (γ : Conₘ 𝕄 m) (p r : M)
                      (z : Term M m) (s : Term M (1+ (1+ m))) (n : Term M m) : Set where
  constructor invUsageNatrec
  field
    {δ η θ δ′} : Conₘ 𝕄 m
    δ▸z  : δ ▸ z
    η▸s  : η ∙ p ∙ r ▸ s
    θ▸n  : θ ▸ n
    δ′≡  : δ′ ≡ η +ᶜ r ·ᶜ (δ ∧ᶜ δ′) +ᶜ p ·ᶜ θ
    γ≤γ′ : γ ≤ᶜ δ ∧ᶜ δ′

-- If γ ▸ natrec p r G z s n then δ ▸ z, δ ∙ r ∙ p ▸ s, η ▸ n and γ ≤ᶜ r* ·ᶜ (δ +ᶜ p ·ᶜ η)

inv-usage-natrec : {m : Nat} {𝕄 : Modality M} {γ : Conₘ 𝕄 m} {p r : M} {z n : Term M m}
                   {G : Term M (1+ m)} {s : Term M (1+ (1+ m))}
                 → γ ▸ natrec p r G z s n → InvUsageNatrec γ p r z s n
inv-usage-natrec (natrecₘ δ▸z δ▸s η▸n X≤γ′) = invUsageNatrec δ▸z δ▸s η▸n X≤γ′ ≤ᶜ-reflexive
-- δ▸z δ▸s η▸n r+ ≤ᶜ-reflexive --δ▸z δ▸s η▸n r+ ≤ᶜ-reflexive
inv-usage-natrec (sub γ▸natrec γ≤γ′) with inv-usage-natrec γ▸natrec
... | invUsageNatrec δ▸z δ▸s η▸n X≤γ′ γ′≤γ″ = invUsageNatrec δ▸z δ▸s η▸n X≤γ′ (≤ᶜ-transitive γ≤γ′ γ′≤γ″)


record InvUsageEmptyrec {n} {M} {𝕄 :  Modality M} (γ : Conₘ 𝕄 n) (t : Term M n) : Set where
  constructor invUsageEmptyrec
  field
    {δ} : Conₘ 𝕄 n
    δ▸t : δ ▸ t
    γ≤δ : γ ≤ᶜ δ

-- If γ ▸ Emptyrec p A t then δ ▸ t and γ ≤ᶜ δ

inv-usage-Emptyrec : γ ▸ Emptyrec p A t → InvUsageEmptyrec γ t
inv-usage-Emptyrec (Emptyrecₘ δ▸t) = invUsageEmptyrec δ▸t ≤ᶜ-reflexive
inv-usage-Emptyrec (sub γ▸et γ≤γ′) with inv-usage-Emptyrec γ▸et
... | invUsageEmptyrec δ▸t γ′≤δ = invUsageEmptyrec δ▸t (≤ᶜ-transitive γ≤γ′ γ′≤δ)

-- If γ ▸ star then γ ≤ᶜ 𝟘ᶜ

inv-usage-star : γ ▸ star → γ ≤ᶜ 𝟘ᶜ
inv-usage-star starₘ = ≤ᶜ-reflexive
inv-usage-star (sub  δ▸star γ≤δ) = ≤ᶜ-transitive γ≤δ (inv-usage-star δ▸star)
