------------------------------------------------------------------------
-- Inversion lemmata for γ ▸[ m ] t
------------------------------------------------------------------------

import Graded.Modality
open import Graded.Usage.Restrictions

module Graded.Usage.Inversion
  {a} {M : Set a}
  (open Graded.Modality M)
  (𝕄 : Modality)
  (R : Usage-restrictions 𝕄)
  where

open Modality 𝕄
open Usage-restrictions R

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Usage 𝕄 R
open import Graded.Modality.Dedicated-nr 𝕄
open import Graded.Modality.Dedicated-nr.Instance
open import Graded.Mode 𝕄
open import Definition.Untyped M hiding (_∙_)

open import Tools.Bool using (T)
open import Tools.Nat using (Nat; 1+; 2+)
open import Tools.Product
open import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Sum

private
  variable
    k n : Nat
    γ χ : Conₘ n
    p q r : M
    A B F t t′ u v z n' : Term n
    G : Term (1+ n)
    m : Mode
    b : BinderMode
    s : Strength

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

inv-usage-Unit : γ ▸[ m ] Unit s → γ ≤ᶜ 𝟘ᶜ
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

-- If γ ▸[ m ] ⟨ b ⟩ p , q ▷ F ▹ G then δ ▸[ m ᵐ· p ] F,
-- η ∙ ⌜ m ⌝ · q ▸[ m ] G and γ ≤ᶜ δ +ᶜ η.

inv-usage-ΠΣ : γ ▸[ m ] ΠΣ⟨ b ⟩ p , q ▷ F ▹ G → InvUsageΠΣ γ m b p q F G
inv-usage-ΠΣ (ΠΣₘ γ▸F δ▸G) = invUsageΠΣ γ▸F δ▸G ≤ᶜ-refl
inv-usage-ΠΣ (sub γ▸Π γ≤γ′) with inv-usage-ΠΣ γ▸Π
… | invUsageΠΣ δ▸F η▸G γ′≤δ+η =
  invUsageΠΣ δ▸F η▸G (≤ᶜ-trans γ≤γ′ γ′≤δ+η)

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


record InvUsageProdʷ
         {n} (γ : Conₘ n) (m : Mode) (p : M) (t u : Term n) :
         Set a where
  constructor invUsageProdʷ
  field
    {δ η} : Conₘ n
    δ▸t   : δ ▸[ m ᵐ· p ] t
    η▸u   : η ▸[ m ] u
    γ≤γ′  : γ ≤ᶜ p ·ᶜ δ +ᶜ η

-- If γ ▸[ m ] prodʷ p t u then δ ▸[ m ᵐ· p ] t, η ▸[ m ] u and
-- γ ≤ᶜ p ·ᶜ δ +ᶜ η.

inv-usage-prodʷ : γ ▸[ m ] prodʷ p t u → InvUsageProdʷ γ m p t u
inv-usage-prodʷ (prodʷₘ γ▸t δ▸u) = invUsageProdʷ γ▸t δ▸u ≤ᶜ-refl
inv-usage-prodʷ (sub γ▸tu γ≤γ′) with inv-usage-prodʷ γ▸tu
... | invUsageProdʷ δ▸t η▸u γ′≤γ″ =
  invUsageProdʷ δ▸t η▸u (≤ᶜ-trans γ≤γ′ γ′≤γ″)

record InvUsageProdˢ
         {n} (γ : Conₘ n) (m : Mode) (p : M) (t u : Term n) :
         Set a where
  constructor invUsageProdˢ
  field
    {δ η}  : Conₘ n
    δ▸t    : δ ▸[ m ᵐ· p ] t
    η▸u    : η ▸[ m ] u
    γ≤pδ∧η : γ ≤ᶜ p ·ᶜ δ ∧ᶜ η

-- If γ ▸[ m ] prod p t u then δ ▸[ m ᵐ· p ] t, η ▸[ m ] u and
-- γ ≤ᶜ p ·ᶜ δ ∧ᶜ η.

inv-usage-prodˢ : γ ▸[ m ] prodˢ p t u → InvUsageProdˢ γ m p t u
inv-usage-prodˢ (prodˢₘ γ▸t γ▸u) = invUsageProdˢ γ▸t γ▸u ≤ᶜ-refl
inv-usage-prodˢ (sub δ▸tu γ≤γ′) with inv-usage-prodˢ δ▸tu
... | invUsageProdˢ δ▸t δ▸u γ′≤δ = invUsageProdˢ δ▸t δ▸u (≤ᶜ-trans γ≤γ′ γ′≤δ)


record InvUsageFst
         {n} (γ : Conₘ n) (m : Mode) (p : M) (t : Term n) :
         Set a where
  constructor invUsageFst
  field
    {δ}          : Conₘ n
    m′           : Mode
    m≡m′ᵐ·p      : m ≡ m′ ᵐ· p
    δ▸t          : δ ▸[ m ] t
    γ≤δ          : γ ≤ᶜ δ
    mp-condition : m PE.≡ 𝟙ᵐ → p ≤ 𝟙

-- If γ ▸[ m ] fst t then m ≡ m′ ᵐ· p, δ ▸[ m ] t and γ ≤ᶜ δ, and
-- furthermore if m ≡ 𝟙 then p ≤ 𝟙.

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
         (t : Term n) (u : Term (2+ n)) : Set a where
  constructor invUsageProdrec
  field
    {δ η θ} : Conₘ n
    δ▸t : δ ▸[ m ᵐ· r ] t
    η▸u : η ∙ ⌜ m ⌝ · r · p ∙ ⌜ m ⌝ · r ▸[ m ] u
    θ▸A : θ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] A
    P : Prodrec-allowed m r p q
    γ≤γ′ : γ ≤ᶜ r ·ᶜ δ +ᶜ η

-- If γ ▸[ m ] prodrec r p q A t u then δ ▸[ m ᵐ· r ] t,
-- η ∙ ⌜ m ⌝ · r · p ∙ ⌜ m ⌝ · r ▸[ m ] u, θ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] A,
-- Prodrec-allowed m r p q and γ ≤ᶜ r ·ᶜ δ +ᶜ η.

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


data InvUsageNatrec′ (p r : M) (γ δ η : Conₘ n) : Conₘ n → Set a where
  invUsageNatrecNr :
    ⦃ has-nr : Dedicated-nr ⦄ →
    InvUsageNatrec′ p r γ δ η (nrᶜ p r γ δ η)
  invUsageNatrecNoNr :
    ⦃ no-nr : No-dedicated-nr ⦄ →
    χ ≤ᶜ γ →
    (T 𝟘ᵐ-allowed →
     χ ≤ᶜ δ) →
    (⦃ 𝟘-well-behaved : Has-well-behaved-zero semiring-with-meet ⦄ →
     χ ≤ᶜ η) →
    χ ≤ᶜ δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ χ →
    InvUsageNatrec′ p r γ δ η χ

data InvUsageNatrec
       (γ : Conₘ k) (m : Mode) (p q r : M) (A : Term (1+ k))
       (z : Term k) (s : Term (2+ k)) (n : Term k) : Set a where
  invUsageNatrec :
    {δ η θ φ χ : Conₘ k} →
    δ ▸[ m ] z →
    η ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · r ▸[ m ] s →
    θ ▸[ m ] n →
    φ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] A →
    γ ≤ᶜ χ →
    InvUsageNatrec′ p r δ η θ χ →
    InvUsageNatrec γ m p q r A z s n

-- An inversion lemma for natrec.

inv-usage-natrec :
  {s : Term (2+ k)} {n : Term k} →
  γ ▸[ m ] natrec p q r G z s n → InvUsageNatrec γ m p q r G z s n
inv-usage-natrec (natrecₘ δ▸z δ▸s η▸n θ▸A) =
  invUsageNatrec δ▸z δ▸s η▸n θ▸A ≤ᶜ-refl invUsageNatrecNr
inv-usage-natrec (natrec-no-nrₘ ▸z ▸s ▸n ▸A χ≤₁ χ≤₂ χ≤₃ χ≤₄) =
  invUsageNatrec ▸z ▸s ▸n ▸A ≤ᶜ-refl
    (invUsageNatrecNoNr χ≤₁ χ≤₂ χ≤₃ χ≤₄)
inv-usage-natrec (sub γ▸natrec γ≤γ′) with inv-usage-natrec γ▸natrec
... | invUsageNatrec δ▸z η▸s θ▸n φ▸A γ′≤γ″ extra =
  invUsageNatrec δ▸z η▸s θ▸n φ▸A (≤ᶜ-trans γ≤γ′ γ′≤γ″) extra

record InvUsageemptyrec
         {n} (γ : Conₘ n) (m : Mode) (p : M) (A t : Term n) :
         Set a where
  constructor invUsageemptyrec
  field
    {δ η} : Conₘ n
    δ▸t  : δ ▸[ m ᵐ· p ] t
    η▸A  : η ▸[ 𝟘ᵐ? ] A
    γ≤pδ : γ ≤ᶜ p ·ᶜ δ

-- If γ ▸[ m ] emptyrec p A t then δ ▸[ m ᵐ· p ] t, η ▸[ 𝟘ᵐ? ] A and
-- γ ≤ᶜ p ·ᶜ δ.

inv-usage-emptyrec :
  γ ▸[ m ] emptyrec p A t → InvUsageemptyrec γ m p A t
inv-usage-emptyrec (emptyrecₘ δ▸t η▸A) = invUsageemptyrec δ▸t η▸A ≤ᶜ-refl
inv-usage-emptyrec (sub γ▸et γ≤γ′) with inv-usage-emptyrec γ▸et
... | invUsageemptyrec δ▸t η▸A γ′≤δ = invUsageemptyrec δ▸t η▸A (≤ᶜ-trans γ≤γ′ γ′≤δ)

-- If γ ▸[ m ] starʷ then γ ≤ᶜ 𝟘ᶜ.

inv-usage-starʷ : γ ▸[ m ] starʷ → γ ≤ᶜ 𝟘ᶜ
inv-usage-starʷ starʷₘ = ≤ᶜ-refl
inv-usage-starʷ (sub  δ▸star γ≤δ) = ≤ᶜ-trans γ≤δ (inv-usage-starʷ δ▸star)

-- If γ ▸[ m ] starˢ and the strong unit type cannot be used as a sink
-- then 𝟘ᶜ ≈ᶜ γ.

inv-usage-starˢ : γ ▸[ m ] starˢ → (¬Starˢ-sink → γ ≤ᶜ 𝟘ᶜ)
inv-usage-starˢ (starˢₘ prop) ¬sink =
  ≤ᶜ-reflexive (≈ᶜ-trans (≈ᶜ-sym (·ᶜ-congˡ (prop ¬sink))) (·ᶜ-zeroʳ _))
inv-usage-starˢ (sub γ▸star γ≤γ′) ¬sink with inv-usage-starˢ γ▸star ¬sink
... | γ′≤𝟘 = ≤ᶜ-trans γ≤γ′ γ′≤𝟘

record InvUsageUnitrec {n} (γ : Conₘ n) (m : Mode) (p q : M)
                       (A : Term (1+ n)) (t u : Term n) : Set a where
  constructor invUsageUnitrec
  field
    {δ η θ} : Conₘ n
    δ▸t : δ ▸[ m ᵐ· p ] t
    η▸u : η ▸[ m ] u
    θ▸A : θ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] A
    P : Unitrec-allowed m p q
    γ≤δ+η : γ ≤ᶜ p ·ᶜ δ +ᶜ η

-- A usage inversion lemma for unitrec.

inv-usage-unitrec : γ ▸[ m ] unitrec p q A t u → InvUsageUnitrec γ m p q A t u
inv-usage-unitrec (unitrecₘ δ▸t η▸u θ▸A ok) =
  invUsageUnitrec δ▸t η▸u θ▸A ok ≤ᶜ-refl
inv-usage-unitrec (sub γ′▸ur γ≤γ′) with inv-usage-unitrec γ′▸ur
... | invUsageUnitrec δ▸t η▸u θ▸A ok γ′≤pδ+η =
  invUsageUnitrec δ▸t η▸u θ▸A ok (≤ᶜ-trans γ≤γ′ γ′≤pδ+η)

-- A type used to state inv-usage-Id.

data InvUsageId
       {n} (γ : Conₘ n) (m : Mode) (A t u : Term n) : Set a where
  invUsageId :
    {δ η θ : Conₘ n} →
    ¬ Id-erased →
    θ ▸[ 𝟘ᵐ? ] A →
    δ ▸[ m ] t →
    η ▸[ m ] u →
    γ ≤ᶜ δ +ᶜ η →
    InvUsageId γ m A t u
  invUsageId₀ :
    {δ η θ : Conₘ n} →
    Id-erased →
    θ ▸[ 𝟘ᵐ? ] A →
    δ ▸[ 𝟘ᵐ? ] t →
    η ▸[ 𝟘ᵐ? ] u →
    γ ≤ᶜ 𝟘ᶜ →
    InvUsageId γ m A t u

-- A usage inversion lemma for Id.

inv-usage-Id : γ ▸[ m ] Id A t u → InvUsageId γ m A t u
inv-usage-Id (Idₘ ok ▸A ▸t ▸u) = invUsageId ok ▸A ▸t ▸u ≤ᶜ-refl
inv-usage-Id (Id₀ₘ ok ▸A ▸t ▸u) = invUsageId₀ ok ▸A ▸t ▸u ≤ᶜ-refl
inv-usage-Id (sub γ′▸ γ≤γ′) with inv-usage-Id γ′▸
... | invUsageId ok ▸t ▸u ▸A γ′≤ =
  invUsageId ok ▸t ▸u ▸A (≤ᶜ-trans γ≤γ′ γ′≤)
... | invUsageId₀ ok ▸t ▸u ▸A γ′≤ =
  invUsageId₀ ok ▸t ▸u ▸A (≤ᶜ-trans γ≤γ′ γ′≤)

-- If γ ▸[ m ] rfl then γ ≤ᶜ 𝟘ᶜ.

inv-usage-rfl : γ ▸[ m ] rfl → γ ≤ᶜ 𝟘ᶜ
inv-usage-rfl rflₘ         = ≤ᶜ-refl
inv-usage-rfl (sub δ▸ γ≤δ) = ≤ᶜ-trans γ≤δ (inv-usage-rfl δ▸)

-- A type used to state inv-usage-J.

data InvUsageJ
       {n} (γ : Conₘ n) (m : Mode) (p q : M) (A t : Term n)
       (B : Term (2+ n)) (u t′ v : Term n) : Set a where
  invUsageJ :
    {γ₁ γ₂ γ₃ γ₄ γ₅ γ₆ : Conₘ n} →
    ¬ Erased-matches-for-J m →
    γ₁ ▸[ 𝟘ᵐ? ] A →
    γ₂ ▸[ m ] t →
    γ₃ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · q ▸[ m ] B →
    γ₄ ▸[ m ] u →
    γ₅ ▸[ m ] t′ →
    γ₆ ▸[ m ] v →
    γ ≤ᶜ ω ·ᶜ (γ₂ ∧ᶜ γ₃ ∧ᶜ γ₄ ∧ᶜ γ₅ ∧ᶜ γ₆) →
    InvUsageJ γ m p q A t B u t′ v
  invUsageJ₀ :
    {γ₁ γ₂ γ₃ γ₄ γ₅ γ₆ : Conₘ n} →
    Erased-matches-for-J m →
    γ₁ ▸[ 𝟘ᵐ? ] A →
    γ₂ ▸[ 𝟘ᵐ? ] t →
    γ₃ ∙ ⌜ 𝟘ᵐ? ⌝ · p ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] B →
    γ₄ ▸[ m ] u →
    γ₅ ▸[ 𝟘ᵐ? ] t′ →
    γ₆ ▸[ 𝟘ᵐ? ] v →
    γ ≤ᶜ γ₄ →
    InvUsageJ γ m p q A t B u t′ v

-- A usage inversion lemma for J.

inv-usage-J :
  γ ▸[ m ] J p q A t B u t′ v → InvUsageJ γ m p q A t B u t′ v
inv-usage-J (Jₘ ok ▸A ▸t ▸B ▸u ▸t′ ▸v) =
  invUsageJ ok ▸A ▸t ▸B ▸u ▸t′ ▸v ≤ᶜ-refl
inv-usage-J (J₀ₘ ok ▸A ▸t ▸B ▸u ▸t′ ▸v) =
  invUsageJ₀ ok ▸A ▸t ▸B ▸u ▸t′ ▸v ≤ᶜ-refl
inv-usage-J (sub γ′▸ γ≤γ′) with inv-usage-J γ′▸
... | invUsageJ ok ▸t ▸B ▸u ▸t′ ▸v ▸A γ′≤ =
  invUsageJ ok ▸t ▸B ▸u ▸t′ ▸v ▸A (≤ᶜ-trans γ≤γ′ γ′≤)
... | invUsageJ₀ ok ▸t ▸B ▸u ▸t′ ▸v ▸A γ′≤ =
  invUsageJ₀ ok ▸t ▸B ▸u ▸t′ ▸v ▸A (≤ᶜ-trans γ≤γ′ γ′≤)

-- A type used to state inv-usage-K.

data InvUsageK
       {n} (γ : Conₘ n) (m : Mode) (p : M) (A t : Term n)
       (B : Term (1+ n)) (u v : Term n) : Set a where
  invUsageK :
    {γ₁ γ₂ γ₃ γ₄ γ₅ : Conₘ n} →
    ¬ Erased-matches-for-K m →
    γ₁ ▸[ 𝟘ᵐ? ] A →
    γ₂ ▸[ m ] t →
    γ₃ ∙ ⌜ m ⌝ · p ▸[ m ] B →
    γ₄ ▸[ m ] u →
    γ₅ ▸[ m ] v →
    γ ≤ᶜ ω ·ᶜ (γ₂ ∧ᶜ γ₃ ∧ᶜ γ₄ ∧ᶜ γ₅) →
    InvUsageK γ m p A t B u v
  invUsageK₀ :
    {γ₁ γ₂ γ₃ γ₄ γ₅ : Conₘ n} →
    Erased-matches-for-K m →
    γ₁ ▸[ 𝟘ᵐ? ] A →
    γ₂ ▸[ 𝟘ᵐ? ] t →
    γ₃ ∙ ⌜ 𝟘ᵐ? ⌝ · p ▸[ 𝟘ᵐ? ] B →
    γ₄ ▸[ m ] u →
    γ₅ ▸[ 𝟘ᵐ? ] v →
    γ ≤ᶜ γ₄ →
    InvUsageK γ m p A t B u v

-- A usage inversion lemma for K.

inv-usage-K : γ ▸[ m ] K p A t B u v → InvUsageK γ m p A t B u v
inv-usage-K (Kₘ ok ▸A ▸t ▸B ▸u ▸v) =
  invUsageK ok ▸A ▸t ▸B ▸u ▸v ≤ᶜ-refl
inv-usage-K (K₀ₘ ok ▸A ▸t ▸B ▸u ▸v) =
  invUsageK₀ ok ▸A ▸t ▸B ▸u ▸v ≤ᶜ-refl
inv-usage-K (sub γ′▸ γ≤γ′) with inv-usage-K γ′▸
... | invUsageK ok ▸t ▸B ▸u ▸v ▸A γ′≤ =
  invUsageK ok ▸t ▸B ▸u ▸v ▸A (≤ᶜ-trans γ≤γ′ γ′≤)
... | invUsageK₀ ok ▸t ▸B ▸u ▸v ▸A γ′≤ =
  invUsageK₀ ok ▸t ▸B ▸u ▸v ▸A (≤ᶜ-trans γ≤γ′ γ′≤)

-- A type used to state inv-usage-[]-cong.

record InvUsage-[]-cong
         {n} (γ : Conₘ n) (A t u v : Term n) : Set a where
  constructor invUsage-[]-cong
  field
    {γ₁ γ₂ γ₃ γ₄} : Conₘ n
    ▸A            : γ₁ ▸[ 𝟘ᵐ? ] A
    ▸t            : γ₂ ▸[ 𝟘ᵐ? ] t
    ▸u            : γ₃ ▸[ 𝟘ᵐ? ] u
    ▸v            : γ₄ ▸[ 𝟘ᵐ? ] v
    ≤𝟘            : γ ≤ᶜ 𝟘ᶜ

-- A usage inversion lemma for []-cong.

inv-usage-[]-cong :
  γ ▸[ m ] []-cong s A t u v → InvUsage-[]-cong γ A t u v
inv-usage-[]-cong ([]-congₘ ▸A ▸t ▸u ▸v) =
  invUsage-[]-cong ▸A ▸t ▸u ▸v ≤ᶜ-refl
inv-usage-[]-cong (sub γ′▸ γ≤γ′) with inv-usage-[]-cong γ′▸
... | invUsage-[]-cong ▸A ▸t ▸u ▸v γ′≤ =
  invUsage-[]-cong ▸A ▸t ▸u ▸v (≤ᶜ-trans γ≤γ′ γ′≤)
