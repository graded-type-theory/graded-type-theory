------------------------------------------------------------------------
-- Inversion lemmata for γ ▸[ m ] t
------------------------------------------------------------------------

open import Definition.Modality

module Definition.Modality.Usage.Inversion
  {a} {M : Set a} (𝕄 : Modality M) where

open Modality 𝕄

open import Definition.Modality.Context 𝕄
open import Definition.Modality.Context.Properties 𝕄
open import Definition.Modality.Usage 𝕄
open import Definition.Mode 𝕄
open import Definition.Untyped M hiding (_∙_)

open import Tools.Bool
open import Tools.Nat
open import Tools.PropositionalEquality as PE
open import Tools.Sum

private
  variable
    k n : Nat
    γ : Conₘ n
    p q r : M
    A F t u z n' : Term n
    G : Term (1+ n)
    m : Mode
    b : BinderMode
    s : SigmaMode

-- If γ ▸[ m ] U then γ ≤ᶜ 𝟘ᶜ.

inv-usage-U : γ ▸[ m ] U → γ ≤ᶜ 𝟘ᶜ
inv-usage-U Uₘ = ≤ᶜ-refl
inv-usage-U (sub γ▸U γ≤δ) = ≤ᶜ-trans γ≤δ (inv-usage-U γ▸U)

-- If γ ▸[ m ] ℕ then γ ≤ᶜ 𝟘ᶜ.

inv-usage-ℕ : γ ▸[ m ] ℕ → γ ≤ᶜ 𝟘ᶜ
inv-usage-ℕ ℕₘ = ≤ᶜ-refl
inv-usage-ℕ (sub γ▸ℕ γ≤δ) = ≤ᶜ-trans γ≤δ (inv-usage-ℕ γ▸ℕ)

-- If γ ▸[ m ] Empty then γ ≤ᶜ 𝟘ᶜ.

inv-usage-Empty : γ ▸[ m ] Empty → γ ≤ᶜ 𝟘ᶜ
inv-usage-Empty Emptyₘ = ≤ᶜ-refl
inv-usage-Empty (sub γ▸⊥ γ≤δ) = ≤ᶜ-trans γ≤δ (inv-usage-Empty γ▸⊥)

-- If γ ▸[ m ] Unit then γ ≤ᶜ 𝟘ᶜ.

inv-usage-Unit : γ ▸[ m ] Unit → γ ≤ᶜ 𝟘ᶜ
inv-usage-Unit Unitₘ = ≤ᶜ-refl
inv-usage-Unit (sub γ▸⊤ γ≤δ) = ≤ᶜ-trans γ≤δ (inv-usage-Unit γ▸⊤)


record InvUsageΠΣ {n} (γ : Conₘ n) (m : Mode) (b : BinderMode) (p q : M)
                 (F : Term n) (G : Term (1+ n)) : Set a where
  constructor invUsageΠΣ
  field
    {δ η} : Conₘ n
    δ▸F   : δ ▸[ m ᵐ· p ] F
    η▸G   : η ∙ ⌜ m ⌝ · q ▸[ m ] G
    γ≤δ+η : γ ≤ᶜ δ +ᶜ η
    ok    : Binder b p q

-- If γ ▸[ m ] ⟨ b ⟩ p , q ▷ F ▹ G then δ ▸[ m ᵐ· p ] F,
-- η ∙ ⌜ m ⌝ · q ▸[ m ] G, γ ≤ᶜ δ +ᶜ η and Binder b p q.

inv-usage-ΠΣ : γ ▸[ m ] ΠΣ⟨ b ⟩ p , q ▷ F ▹ G → InvUsageΠΣ γ m b p q F G
inv-usage-ΠΣ (ΠΣₘ γ▸F δ▸G ok) = invUsageΠΣ γ▸F δ▸G ≤ᶜ-refl ok
inv-usage-ΠΣ (sub γ▸Π γ≤γ′) with inv-usage-ΠΣ γ▸Π
… | invUsageΠΣ δ▸F η▸G γ′≤δ+η ok =
  invUsageΠΣ δ▸F η▸G (≤ᶜ-trans γ≤γ′ γ′≤δ+η) ok

-- If γ ▸[ m ] var x then γ ≤ᶜ (𝟘ᶜ , x ≔ ⌜ m ⌝).

inv-usage-var : ∀ {x} {γ : Conₘ n}
              → γ ▸[ m ] var x → γ ≤ᶜ (𝟘ᶜ , x ≔ ⌜ m ⌝)
inv-usage-var var = ≤ᶜ-refl
inv-usage-var (sub γ▸x γ≤γ′) with inv-usage-var γ▸x
... | γ′≤δ = ≤ᶜ-trans γ≤γ′ γ′≤δ


record InvUsageLam
         {n} (γ : Conₘ n) (m : Mode) (p : M) (t : Term (1+ n)) :
         Set a where
  constructor invUsageLam
  field
    {δ} : Conₘ n
    δ▸t : δ ∙ ⌜ m ⌝ · p ▸[ m ] t
    γ≤δ : γ ≤ᶜ δ

-- If γ ▸[ m ] lam p t then δ ∙ ⌜ m ⌝ · p ▸[ m ] t and γ ≤ᶜ δ.

inv-usage-lam : γ ▸[ m ] lam p t → InvUsageLam γ m p t
inv-usage-lam (lamₘ γ▸λpt) = invUsageLam γ▸λpt ≤ᶜ-refl
inv-usage-lam (sub γ′▸λpt γ≤γ′) with inv-usage-lam γ′▸λpt
... | invUsageLam δ▸t γ′≤δ = invUsageLam δ▸t (≤ᶜ-trans γ≤γ′ γ′≤δ)


record InvUsageApp
         {n} (γ : Conₘ n) (t : Term n) (m : Mode) (p : M) (u : Term n) :
         Set a where
  constructor invUsageApp
  field
    {δ η} : Conₘ n
    δ▸t   : δ ▸[ m ] t
    η▸u   : η ▸[ m ᵐ· p ] u
    γ≤δ+η : γ ≤ᶜ δ +ᶜ p ·ᶜ η

-- If γ ▸[ m ] t ∘⟨ p ⟩ u then δ ▸[ m ] t, η ▸[ m ᵐ· p ] u and
-- γ ≤ᶜ δ +ᶜ p ·ᶜ η.

inv-usage-app : γ ▸[ m ] t ∘⟨ p ⟩ u → InvUsageApp γ t m p u
inv-usage-app (γ▸t ∘ₘ δ▸u) = invUsageApp γ▸t δ▸u ≤ᶜ-refl
inv-usage-app (sub γ▸t∘p▷u γ′≤γ) with inv-usage-app γ▸t∘p▷u
... | invUsageApp δ▸t η▸u γ≤δ+pη = invUsageApp δ▸t η▸u (≤ᶜ-trans γ′≤γ γ≤δ+pη)


record InvUsageProdᵣ
         {n} (γ : Conₘ n) (m : Mode) (p : M) (t u : Term n) :
         Set a where
  constructor invUsageProdᵣ
  field
    {δ η} : Conₘ n
    δ▸t   : δ ▸[ m ᵐ· p ] t
    η▸u   : η ▸[ m ] u
    γ≤γ′  : γ ≤ᶜ p ·ᶜ δ +ᶜ η

-- If γ ▸[ m ] prodᵣ p t u then δ ▸[ m ᵐ· p ] t, η ▸[ m ] u and
-- γ ≤ᶜ p ·ᶜ δ +ᶜ η.

inv-usage-prodᵣ : γ ▸[ m ] prodᵣ p t u → InvUsageProdᵣ γ m p t u
inv-usage-prodᵣ (prodᵣₘ γ▸t δ▸u) = invUsageProdᵣ γ▸t δ▸u ≤ᶜ-refl
inv-usage-prodᵣ (sub γ▸tu γ≤γ′) with inv-usage-prodᵣ γ▸tu
... | invUsageProdᵣ δ▸t η▸u γ′≤γ″ =
  invUsageProdᵣ δ▸t η▸u (≤ᶜ-trans γ≤γ′ γ′≤γ″)

record InvUsageProdₚ
         {n} (γ : Conₘ n) (m : Mode) (p : M) (t u : Term n) :
         Set a where
  constructor invUsageProdₚ
  field
    {δ η}  : Conₘ n
    δ▸t    : δ ▸[ m ᵐ· p ] t
    η▸u    : η ▸[ m ] u
    γ≤pδ∧η : γ ≤ᶜ p ·ᶜ δ ∧ᶜ η

-- If γ ▸[ m ] prod p t u then δ ▸[ m ᵐ· p ] t, η ▸[ m ] u and
-- γ ≤ᶜ p ·ᶜ δ ∧ᶜ η.

inv-usage-prodₚ : γ ▸[ m ] prodₚ p t u → InvUsageProdₚ γ m p t u
inv-usage-prodₚ (prodₚₘ γ▸t γ▸u) = invUsageProdₚ γ▸t γ▸u ≤ᶜ-refl
inv-usage-prodₚ (sub δ▸tu γ≤γ′) with inv-usage-prodₚ δ▸tu
... | invUsageProdₚ δ▸t δ▸u γ′≤δ = invUsageProdₚ δ▸t δ▸u (≤ᶜ-trans γ≤γ′ γ′≤δ)


record InvUsageFst
         {n} (γ : Conₘ n) (m : Mode) (p : M) (t : Term n) :
         Set a where
  constructor invUsageFst
  field
    {δ}         : Conₘ n
    m′          : Mode
    m≡m′ᵐ·p     : m ≡ m′ ᵐ· p
    δ▸t         : δ ▸[ m ] t
    γ≤δ         : γ ≤ᶜ δ
    𝟘-condition : (p ≤ 𝟙) ⊎ T 𝟘ᵐ-allowed

-- If γ ▸[ m ] fst t then m ≡ m′ ᵐ· p, δ ▸[ m ] t and γ ≤ᶜ δ, and
-- furthermore one of p ≤ 𝟙 and T 𝟘ᵐ-allowed hold.

inv-usage-fst : γ ▸[ m ] fst p t → InvUsageFst γ m p t
inv-usage-fst (fstₘ m ▸t PE.refl ok) =
  invUsageFst m PE.refl ▸t ≤ᶜ-refl ok
inv-usage-fst (sub ▸t γ≤γ′) with inv-usage-fst ▸t
... | invUsageFst m m≡ ▸t γ′≤ ok =
  invUsageFst m m≡ ▸t (≤ᶜ-trans γ≤γ′ γ′≤) ok

record InvUsageSnd
         {n} (γ : Conₘ n) (m : Mode) (t : Term n) : Set a where
  constructor invUsageSnd
  field
    {δ} : Conₘ n
    δ▸t : δ ▸[ m ] t
    γ≤δ : γ ≤ᶜ δ

-- If γ ▸[ m ] snd t then δ ▸[ m ] t and γ ≤ᶜ δ.

inv-usage-snd : γ ▸[ m ] snd p t → InvUsageSnd γ m t
inv-usage-snd (sndₘ ▸t) = invUsageSnd ▸t ≤ᶜ-refl
inv-usage-snd (sub ▸t γ≤γ′) with inv-usage-snd ▸t
... | invUsageSnd ▸t γ′≤ = invUsageSnd ▸t (≤ᶜ-trans γ≤γ′ γ′≤)

record InvUsageProdrec
         {n} (γ : Conₘ n) (m : Mode) (r p q : M) (A : Term (1+ n))
         (t : Term n) (u : Term (1+ (1+ n))) : Set a where
  constructor invUsageProdrec
  field
    {δ η θ} : Conₘ n
    δ▸t : δ ▸[ m ᵐ· r ] t
    η▸u : η ∙ ⌜ m ⌝ · r · p ∙ ⌜ m ⌝ · r ▸[ m ] u
    θ▸A : θ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] A
    P : Prodrec r p q
    γ≤γ′ : γ ≤ᶜ r ·ᶜ δ +ᶜ η

-- If γ ▸[ m ] prodrec r p q A t u then δ ▸[ m ᵐ· r ] t,
-- η ∙ ⌜ m ⌝ · r · p ∙ ⌜ m ⌝ · r ▸[ m ] u, θ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] A,
-- Prodrec r p and γ ≤ᶜ r ·ᶜ δ +ᶜ η.

inv-usage-prodrec :
  γ ▸[ m ] prodrec r p q A t u → InvUsageProdrec γ m r p q A t u
inv-usage-prodrec (prodrecₘ γ▸t δ▸u η▸A P) = invUsageProdrec γ▸t δ▸u η▸A P ≤ᶜ-refl
inv-usage-prodrec (sub γ▸t γ≤γ′) with inv-usage-prodrec γ▸t
... | invUsageProdrec δ▸t η▸u θ▸A P γ′≤γ″ = invUsageProdrec δ▸t η▸u θ▸A P (≤ᶜ-trans γ≤γ′ γ′≤γ″)

-- If γ ▸[ m ] zero then γ ≤ᶜ 𝟘ᶜ.

inv-usage-zero : γ ▸[ m ] zero → γ ≤ᶜ 𝟘ᶜ
inv-usage-zero zeroₘ = ≤ᶜ-refl
inv-usage-zero (sub  δ▸zero γ≤δ) = ≤ᶜ-trans γ≤δ (inv-usage-zero δ▸zero)


record InvUsageSuc
         {n} (γ : Conₘ n) (m : Mode) (t : Term n) : Set a where
  constructor invUsageSuc
  field
    {δ} : Conₘ n
    δ▸t : δ ▸[ m ] t
    γ≤δ : γ ≤ᶜ δ

-- If γ ▸[ m ] suc t then δ ▸[ m ] t and γ ≤ᶜ δ.

inv-usage-suc : γ ▸[ m ] suc t → InvUsageSuc γ m t
inv-usage-suc (sucₘ γ▸t) = invUsageSuc γ▸t ≤ᶜ-refl
inv-usage-suc (sub γ▸st γ≤γ′) with inv-usage-suc γ▸st
... | invUsageSuc δ▸t γ′≤δ = invUsageSuc δ▸t (≤ᶜ-trans γ≤γ′ γ′≤δ)


record InvUsageNatrec
         (γ : Conₘ k) (m : Mode) (p q r : M) (A : Term (1+ k))
         (z : Term k) (s : Term (1+ (1+ k))) (n : Term k) : Set a where
  constructor invUsageNatrec
  field
    {δ η θ φ} : Conₘ k
    δ▸z  : δ ▸[ m ] z
    η▸s  : η ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · r ▸[ m ] s
    θ▸n  : θ ▸[ m ] n
    φ▸A  : φ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] A
    γ≤γ′ : γ ≤ᶜ (δ ∧ᶜ θ) ⊛ᶜ (η +ᶜ p ·ᶜ θ) ▷ r

-- If γ ▸[ m ] natrec p r G z s n, then δ ▸[ m ] z,
-- η ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · r ▸[ m ] s, θ ▸[ m ] n,
-- φ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] A and γ ≤ᶜ (δ ∧ᶜ θ) ⊛ᶜ (η +ᶜ p ·ᶜ θ) ▷ r.

inv-usage-natrec :
  {s : Term (1+ (1+ k))} {n : Term k} →
  γ ▸[ m ] natrec p q r G z s n → InvUsageNatrec γ m p q r G z s n
inv-usage-natrec (natrecₘ δ▸z δ▸s η▸n θ▸A) = invUsageNatrec δ▸z δ▸s η▸n θ▸A ≤ᶜ-refl
inv-usage-natrec (sub γ▸natrec γ≤γ′) with inv-usage-natrec γ▸natrec
... | invUsageNatrec δ▸z η▸s θ▸n φ▸A γ′≤γ″ = invUsageNatrec δ▸z η▸s θ▸n φ▸A (≤ᶜ-trans γ≤γ′ γ′≤γ″)


record InvUsageEmptyrec
         {n} (γ : Conₘ n) (m : Mode) (p : M) (A t : Term n) :
         Set a where
  constructor invUsageEmptyrec
  field
    {δ η} : Conₘ n
    δ▸t  : δ ▸[ m ᵐ· p ] t
    η▸A  : η ▸[ 𝟘ᵐ? ] A
    γ≤pδ : γ ≤ᶜ p ·ᶜ δ

-- If γ ▸[ m ] Emptyrec p A t then δ ▸[ m ᵐ· p ] t, η ▸[ 𝟘ᵐ? ] A and
-- γ ≤ᶜ p ·ᶜ δ.

inv-usage-Emptyrec :
  γ ▸[ m ] Emptyrec p A t → InvUsageEmptyrec γ m p A t
inv-usage-Emptyrec (Emptyrecₘ δ▸t η▸A) = invUsageEmptyrec δ▸t η▸A ≤ᶜ-refl
inv-usage-Emptyrec (sub γ▸et γ≤γ′) with inv-usage-Emptyrec γ▸et
... | invUsageEmptyrec δ▸t η▸A γ′≤δ = invUsageEmptyrec δ▸t η▸A (≤ᶜ-trans γ≤γ′ γ′≤δ)

-- If γ ▸[ m ] star then γ ≤ᶜ 𝟘ᶜ.

inv-usage-star : γ ▸[ m ] star → γ ≤ᶜ 𝟘ᶜ
inv-usage-star starₘ = ≤ᶜ-refl
inv-usage-star (sub  δ▸star γ≤δ) = ≤ᶜ-trans γ≤δ (inv-usage-star δ▸star)
