------------------------------------------------------------------------
-- Properties related to the usage relation for the "Zero-one" mode
-- structure.
------------------------------------------------------------------------

import Graded.Modality
import Graded.Mode.Instances.Zero-one
open import Graded.Mode.Instances.Zero-one.Variant
open import Graded.Usage.Restrictions

module Graded.Usage.Properties.Zero-one
  {a} {M : Set a}
  (open Graded.Modality M)
  {𝕄 : Modality}
  (open Modality 𝕄)
  (mode-variant : Mode-variant 𝕄)
  (open Graded.Mode.Instances.Zero-one mode-variant)
  (R : Usage-restrictions 𝕄 Zero-one-isMode)
  where

open Usage-restrictions R
open Mode-variant mode-variant

open import Definition.Untyped M

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Modality.Properties 𝕄
open import Graded.Usage R
open import Graded.Usage.Inversion R
open import Graded.Usage.Properties R
open import Graded.Usage.Restrictions.Natrec 𝕄
open import Graded.Usage.Restrictions.Instance R

open import Tools.Bool
open import Tools.Empty
open import Tools.Function
open import Tools.Nat using (Nat; 1+; 2+)
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation
import Tools.Reasoning.PropositionalEquality
open import Tools.Sum

private variable
  k : Nat
  γ δ η θ χ : Conₘ _
  m m′ m₁ m₂ : Mode
  p q r : M
  t A z s n : Term _
  ok : T _
  ∇ : DCon _ _

------------------------------------------------------------------------
-- Variants of usage rules and inversion lemmas.

opaque

  -- An alternative formulation of the mode condition in the usage rule
  -- for fst

  fst-alt-mp-cond : ⌜ m ⌝ · p ≤ ⌜ m ⌝ ⇔ (m ≡ 𝟙ᵐ → p ≤ 𝟙)
  fst-alt-mp-cond {p} = lemma₁ _ , lemma₂ _
    where
    open ≤-reasoning
    lemma₁ : ∀ m → (⌜ m ⌝ · p ≤ ⌜ m ⌝) → m ≡ 𝟙ᵐ → p ≤ 𝟙
    lemma₁ 𝟘ᵐ mp≤m ()
    lemma₁ 𝟙ᵐ mp≤m refl = begin
      p           ≈˘⟨ ·-identityˡ _ ⟩
      𝟙 · p       ≈˘⟨ ·-congʳ ⌜𝟙ᵐ⌝ ⟩
      ⌜ 𝟙ᵐ ⌝ · p  ≤⟨ mp≤m ⟩
      ⌜ 𝟙ᵐ ⌝      ≈⟨ ⌜𝟙ᵐ⌝ ⟩
      𝟙           ∎
    lemma₂ : ∀ m → (m ≡ 𝟙ᵐ → p ≤ 𝟙) → ⌜ m ⌝ · p ≤ ⌜ m ⌝
    lemma₂ 𝟘ᵐ p≤𝟙 = begin
      ⌜ 𝟘ᵐ ⌝ · p  ≡⟨⟩
      𝟘 · p       ≈⟨ ·-zeroˡ _ ⟩
      𝟘           ≡⟨⟩
      ⌜ 𝟘ᵐ ⌝      ∎
    lemma₂ 𝟙ᵐ p≤𝟙 = begin
      ⌜ 𝟙ᵐ ⌝ · p  ≈⟨ ·-congʳ ⌜𝟙ᵐ⌝ ⟩
      𝟙 · p       ≈⟨ ·-identityˡ _ ⟩
      p           ≤⟨ p≤𝟙 refl ⟩
      𝟙           ≈˘⟨ ⌜𝟙ᵐ⌝ ⟩
      ⌜ 𝟙ᵐ ⌝      ∎

opaque

  -- An alternative usage rule for fst

  fstₘ₀₁ :
    ∀ m →
    γ ▸[ m ᵐ· p ] t →
    m ᵐ· p ≡ m′ →
    (m′ ≡ 𝟙ᵐ → p ≤ 𝟙) →
    γ ▸[ m′ ] fst p t
  fstₘ₀₁ m ▸t refl mp-cond =
    fstₘ ▸t (fst-alt-mp-cond .proj₂ mp-cond)

opaque

  -- An alternative usage inversion lemma for fst

  inv-usage-fst₀₁ :
    γ ▸[ m ] fst p t →
    ∃₂ λ δ m′ → m ≡ m′ ᵐ· p × δ ▸[ m ] t × γ ≤ᶜ δ × (m ≡ 𝟙ᵐ → p ≤ 𝟙)
  inv-usage-fst₀₁ {m} ▸t =
    let invUsageFst ▸t γ≤ mp-cond = inv-usage-fst ▸t
        mp-cond′ = fst-alt-mp-cond .proj₁ mp-cond
        m≡ = lemma m mp-cond′
    in  _ , _ , m≡ , ▸t , γ≤ , mp-cond′
    where
    open Tools.Reasoning.PropositionalEquality
    lemma : ∀ m → (m ≡ 𝟙ᵐ → p ≤ 𝟙) → m ≡ m ᵐ· p
    lemma {p} 𝟘ᵐ _ =  begin
      𝟘ᵐ       ≡˘⟨ 𝟘ᵐ?≡𝟘ᵐ ⟩
      𝟘ᵐ?      ≡˘⟨ ᵐ·-zeroˡ ⟩
      𝟘ᵐ? ᵐ· p ≡⟨ ᵐ·-congʳ 𝟘ᵐ?≡𝟘ᵐ ⟩
      𝟘ᵐ ᵐ· p  ∎
    lemma {p} 𝟙ᵐ p≤𝟙 =
      𝟙ᵐ      ≡˘⟨ 𝟘ᵐ-allowed-elim (λ ok → ≢𝟘→⌞⌟≡𝟙ᵐ (λ { refl → 𝟘ᵐ.𝟘≰𝟙 ok (p≤𝟙 refl)})) only-𝟙ᵐ-without-𝟘ᵐ ⟩
      ⌞ p ⌟   ≡˘⟨ ᵐ·-identityˡ ⟩
      𝟙ᵐ ᵐ· p ∎

opaque

  -- An alternative usage rule for natrec corresponding to natrec-no-nrₘ

  natrec-no-nrₘ₀₁ :
    ⦃ no-nr : Nr-not-available ⦄ →
    γ ▸[ m ] z →
    δ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · r ▸[ m ] s →
    η ▸[ m ] n →
    θ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] A →
    χ ≤ᶜ γ →
    (T 𝟘ᵐ-allowed →
     χ ≤ᶜ δ) →
    (⦃ 𝟘-well-behaved :
         Has-well-behaved-zero 𝕄 ⦄ →
     χ ≤ᶜ η) →
     χ ≤ᶜ δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ χ →
     χ ▸[ m ] natrec p q r A z s n
  natrec-no-nrₘ₀₁ ▸z ▸s ▸n ▸A le₁ le₂ le₃ le₄ =
    natrec-no-nrₘ ▸z ▸s ▸n ▸A le₁
      (le₂ ∘→ ¬Trivialᵐ→𝟘ᵐ-allowed)
      (λ ok → case trivialᵐ? of λ where
        (yes 𝟙ᵐ≡𝟘ᵐ) → le₃ ⦃ ok 𝟙ᵐ≡𝟘ᵐ ⦄
        (no 𝟙ᵐ≢𝟘ᵐ) → le₃ ⦃ 𝟘-well-behaved (¬Trivialᵐ→𝟘ᵐ-allowed 𝟙ᵐ≢𝟘ᵐ) ⦄)
      le₄

opaque

  -- An alternative inversion lemma for natrec with Nr-not-available

  inv-usage-natrec-no-nr₀₁ :
    ⦃ no-nr : Nr-not-available ⦄ →
    γ ▸[ m ] natrec p q r A z s n →
    ∃₅ λ δ η θ φ χ → δ ▸[ m ] z ×
    η ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · r ▸[ m ] s ×
    θ ▸[ m ] n × φ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] A ×
    γ ≤ᶜ χ × χ ≤ᶜ δ × (T 𝟘ᵐ-allowed → χ ≤ᶜ η) ×
    (⦃ _ : Has-well-behaved-zero 𝕄 ⦄ → χ ≤ᶜ θ) ×
    χ ≤ᶜ η +ᶜ p ·ᶜ θ +ᶜ r ·ᶜ χ
  inv-usage-natrec-no-nr₀₁ ▸nr =
    let δ , η , θ , φ , χ , ▸z , ▸s , ▸n , ▸A
          , le₁ , le₂ , le₃ , le₄ , le₅ = inv-usage-natrec-no-nr ▸nr
    in  δ , η , θ , φ , χ , ▸z , ▸s , ▸n , ▸A
          , le₁ , le₂ , le₃ ∘→ 𝟘ᵐ-allowed→¬Trivialᵐ
          , (λ ⦃ 𝟘-well-behaved ⦄ → le₄ (λ _ → 𝟘-well-behaved))
          , le₅

data InvUsageNatrec′₀₁ (p r : M) (γ δ η : Conₘ k) : Conₘ k → Set a where
  invUsageNatrecNr :
    ⦃ has-nr : Nr-available ⦄ →
    InvUsageNatrec′₀₁ p r γ δ η (nrᶜ p r γ δ η)
  invUsageNatrecNoNr :
    ⦃ no-nr : Nr-not-available ⦄ →
    χ ≤ᶜ γ →
    (¬ Trivialᵐ →
     χ ≤ᶜ δ) →
    (⦃ 𝟘-well-behaved : Has-well-behaved-zero 𝕄 ⦄ → χ ≤ᶜ η) →
    χ ≤ᶜ δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ χ →
    InvUsageNatrec′₀₁ p r γ δ η χ
  invUsageNatrecNoNrGLB :
    ∀ {x} →
    ⦃ no-nr : Nr-not-available-GLB ⦄ →
    Greatest-lower-bound x (nrᵢ r 𝟙 p) →
    Greatest-lower-boundᶜ χ (nrᵢᶜ r γ δ) →
    InvUsageNatrec′₀₁ p r γ δ η (x ·ᶜ η +ᶜ χ)

data InvUsageNatrec₀₁
       (γ : Conₘ k) (m : Mode) (p q r : M) (A : Term (1+ k))
       (z : Term k) (s : Term (2+ k)) (n : Term k) : Set a where
  invUsageNatrec :
    {δ η θ φ χ : Conₘ k} →
    δ ▸[ m ] z →
    η ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · r ▸[ m ] s →
    θ ▸[ m ] n →
    φ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] A →
    γ ≤ᶜ χ →
    InvUsageNatrec′₀₁ p r δ η θ χ →
    InvUsageNatrec₀₁ γ m p q r A z s n

opaque

  -- An alternative inversion lemma for natrec

  inv-usage-natrec₀₁ :
    γ ▸[ m ] natrec p q r A z s n → InvUsageNatrec₀₁ γ m p q r A z s n
  inv-usage-natrec₀₁ ▸nr =
    case inv-usage-natrec ▸nr of λ where
      (invUsageNatrec δ▸z η▸s θ▸n φ▸A γ′≤γ″ extra) →
        invUsageNatrec δ▸z η▸s θ▸n φ▸A γ′≤γ″ $ case extra of λ where
          invUsageNatrecNr → invUsageNatrecNr
          (invUsageNatrecNoNr le₁ le₂ le₃ le₄) →
            invUsageNatrecNoNr le₁ le₂
              (λ ⦃ 𝟘-well-behaved = 𝟘-well-behaved₁ ⦄ →
                 le₃ (λ z₁ → 𝟘-well-behaved₁))
              le₄
          (invUsageNatrecNoNrGLB x-GLB χ-GLB) →
            invUsageNatrecNoNrGLB x-GLB χ-GLB

------------------------------------------------------------------------
-- Properties of the usage relation.

opaque

  -- If 𝟘ᵐ is not allowed, then one can convert usage modes freely.

  ▸-without-𝟘ᵐ : ¬ T 𝟘ᵐ-allowed → γ ▸[ m ] t → γ ▸[ m′ ] t
  ▸-without-𝟘ᵐ not-ok =
    ▸-cong (Mode-propositional-without-𝟘ᵐ not-ok)

opaque

  -- If a term is well-resourced with respect to any context and mode,
  -- then it is well-resourced with respect to the zero usage context
  -- and the mode 𝟘ᵐ[ ok ].

  ▸-𝟘₀₁ : γ ▸[ m ] t → 𝟘ᶜ ▸[ 𝟘ᵐ[ ok ] ] t
  ▸-𝟘₀₁ {ok} ▸t = ▸-cong 𝟘ᵐ?≡𝟘ᵐ (▸-𝟘′ (𝟘ᵐ-allowed→¬Trivialᵐ ok) ▸t)

opaque

  -- A variant of ▸-𝟘.

  𝟘ᶜ▸[𝟘ᵐ?] : T 𝟘ᵐ-allowed → γ ▸[ m ] t → 𝟘ᶜ ▸[ 𝟘ᵐ? ] t
  𝟘ᶜ▸[𝟘ᵐ?] ok = ▸-cong (sym $ 𝟘ᵐ?≡𝟘ᵐ {ok = ok}) ∘→ ▸-𝟘₀₁

opaque

  -- If a term is well-resourced with respect to any context and mode,
  -- then it is well-resourced with respect to some usage context and
  -- the mode 𝟘ᵐ?.

  ▸-𝟘ᵐ? : γ ▸[ m ] t → ∃ λ δ → δ ▸[ 𝟘ᵐ? ] t
  ▸-𝟘ᵐ? ▸t = _ , ▸-𝟘 ▸t

opaque

  -- If a term is well-resourced with respect to ε and any mode, then
  -- it is well-resourced with respect to ε and the mode 𝟘ᵐ?.

  ε-▸-𝟘ᵐ? : ε ▸[ m ] t → ε ▸[ 𝟘ᵐ? ] t
  ε-▸-𝟘ᵐ? = ε-▸-𝟘ᵐ

opaque

  -- A variant of ε-▸-𝟘ᵐ?.

  ▸-𝟘ᵐ?-DCon : ▸[ m ] ∇ → ▸[ 𝟘ᵐ? ] ∇
  ▸-𝟘ᵐ?-DCon = ▸-𝟘ᵐ-DCon

opaque

  -- If γ ▸[ 𝟘ᵐ[ ok ] ] t, then γ ≤ᶜ 𝟘ᶜ.

  ▸-𝟘ᵐ₀₁ : γ ▸[ 𝟘ᵐ[ ok ] ] t → γ ≤ᶜ 𝟘ᶜ
  ▸-𝟘ᵐ₀₁ {ok} ▸t =
    ▸-𝟘ᵐ (𝟘ᵐ-allowed→¬Trivialᵐ ok) (▸-cong (sym 𝟘ᵐ?≡𝟘ᵐ) ▸t)

------------------------------------------------------------------------
-- Inversion lemmas

opaque

  -- A kind of inversion lemma for _▸[_]_ related to multiplication.

  ▸-⌞·⌟ :
    ⌜ ⌞ p · q ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p · q ⌟ ] t →
    (⌜ ⌞ p ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p ⌟ ] t) ⊎ (⌜ ⌞ q ⌟ ⌝ ·ᶜ γ ▸[ ⌞ q ⌟ ] t)
  ▸-⌞·⌟ {p = p} {q = q} {γ = γ} ▸t =
    lemma _ _ refl refl
      (subst (λ m → ⌜ m ⌝ ·ᶜ _ ▸[ m ] _) (sym ⌞⌟·ᵐ) ▸t)
    where
    lemma :
      ∀ m₁ m₂ → ⌞ p ⌟ ≡ m₁ → ⌞ q ⌟ ≡ m₂ →
      ⌜ m₁ ·ᵐ m₂ ⌝ ·ᶜ γ ▸[ m₁ ·ᵐ m₂ ] t →
      (⌜ m₁ ⌝ ·ᶜ γ ▸[ m₁ ] t) ⊎ (⌜ m₂ ⌝ ·ᶜ γ ▸[ m₂ ] t)
    lemma 𝟘ᵐ _  _ _ ▸t = inj₁ ▸t
    lemma 𝟙ᵐ 𝟘ᵐ _ _ ▸t = inj₂ ▸t
    lemma 𝟙ᵐ 𝟙ᵐ _ _ ▸t = inj₁ ▸t

opaque

  -- If m₂ is 𝟘ᵐ[ ok ] whenever m₁ is 𝟘ᵐ[ ok ], then one can convert
  -- from ⌜ m₁ ⌝ ·ᶜ γ ▸[ m₁ ] t to ⌜ m₂ ⌝ ·ᶜ γ ▸[ m₂ ] t.

  ▸-conv :
    (∀ ok → m₁ ≡ 𝟘ᵐ[ ok ] → m₂ ≡ 𝟘ᵐ[ ok ]) →
    ⌜ m₁ ⌝ ·ᶜ γ ▸[ m₁ ] t →
    ⌜ m₂ ⌝ ·ᶜ γ ▸[ m₂ ] t
  ▸-conv {m₁ = 𝟘ᵐ} {m₂ = 𝟘ᵐ} _ ▸t =
    ▸-cong 𝟘ᵐ-cong ▸t
  ▸-conv {m₁ = 𝟙ᵐ} {m₂ = 𝟙ᵐ} _ ▸t =
    ▸t
  ▸-conv {m₁ = 𝟘ᵐ} {m₂ = 𝟙ᵐ} 𝟘ᵐ≡𝟘ᵐ→𝟙ᵐ≡𝟘ᵐ ▸t =
    case 𝟘ᵐ≡𝟘ᵐ→𝟙ᵐ≡𝟘ᵐ _ refl of λ ()
  ▸-conv {m₁ = 𝟙ᵐ} {m₂ = 𝟘ᵐ} {γ = γ} hyp ▸t = sub
    (▸-· {m′ = 𝟘ᵐ} ▸t)
    (begin
      𝟘 ·ᶜ γ       ≈˘⟨ ·ᶜ-congˡ (·ᶜ-identityˡ _) ⟩
      𝟘 ·ᶜ 𝟙 ·ᶜ γ  ∎)
    where
    open ≤ᶜ-reasoning

------------------------------------------------------------------------
-- Properties of usage inference.

opaque

  -- The context ⌈ t ⌉ 𝟘ᵐ[ ok ] is equivalent to 𝟘ᶜ.

  ⌈⌉-𝟘ᵐ₀₁ :
    ⦃ ok′ : Natrec-mode-supports-usage-inference natrec-mode ⦄ →
    (t : Term k) → ⌈ t ⌉ 𝟘ᵐ[ ok ] ≈ᶜ 𝟘ᶜ
  ⌈⌉-𝟘ᵐ₀₁ {ok} t =
    subst (λ m → ⌈ t ⌉ m ≈ᶜ 𝟘ᶜ) 𝟘ᵐ?≡𝟘ᵐ
      (⌈⌉-𝟘ᵐ (𝟘ᵐ-allowed→¬Trivialᵐ ok) t)
