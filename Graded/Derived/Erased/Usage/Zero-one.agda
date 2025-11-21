------------------------------------------------------------------------
-- Some properties related to usage and Erased for the Zero-one mode
-- structure. See also Graded.Derived.Erased.Usage
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Mode.Instances.Zero-one.Variant
import Graded.Mode.Instances.Zero-one
open import Graded.Usage.Restrictions
open import Definition.Untyped.NotParametrised using (Strength)

module Graded.Derived.Erased.Usage.Zero-one
  {a} {M : Set a}
  {𝕄 : Modality M}
  {mode-variant : Mode-variant 𝕄}
  (open Graded.Mode.Instances.Zero-one mode-variant)
  (R : Usage-restrictions 𝕄 Zero-one-isMode)
  (s : Strength)
  where

open Modality 𝕄
open Mode-variant mode-variant
open Usage-restrictions R

open import Graded.Context 𝕄
import Graded.Derived.Erased.Usage R s as U
open import Graded.Modality.Properties 𝕄
open import Graded.Usage R
open import Graded.Usage.Properties R

open import Definition.Untyped M
open import Definition.Untyped.Erased 𝕄 s
import Graded.Derived.Erased.Usage.Eta R as Eta
import Graded.Derived.Erased.Usage.No-eta R as NoEta

open import Tools.Bool using (T)
open import Tools.Empty
open import Tools.Function
open import Tools.Product as Σ
open import Tools.PropositionalEquality as PE using (_≡_)
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation

private variable
  A B t u v w             : Term _
  γ γ₁ γ₂ γ₃ γ₄ γ₅ γ₆ δ η : Conₘ _
  p                       : M
  m                       : Mode
  ok                      : T _

------------------------------------------------------------------------
-- Usage rules

opaque

  -- A usage rule for erased.

  ▸erased′ :
    (s ≡ 𝕨 → ¬ T 𝟘ᵐ-allowed → Trivial) →
    (s ≡ 𝕨 → Prodrec-allowed 𝟘ᵐ? (𝟘 ∧ 𝟙) 𝟘 𝟘) →
    (s ≡ 𝕤 → ¬ T 𝟘ᵐ-allowed → 𝟘 ≤ 𝟙) →
    γ ▸[ 𝟘ᵐ? ] t →
    (s ≡ 𝕨 → ∃ λ δ → δ ▸[ 𝟘ᵐ? ] A) →
    𝟘ᶜ ▸[ 𝟘ᵐ? ] erased A t
  ▸erased′ {γ} trivial ok 𝟘≤𝟙 =
    U.▸erased′ (λ s≡𝕨 → trivial s≡𝕨 ∘→ Trivialᵐ→¬𝟘ᵐ-allowed)
      ok (λ s≡𝕤 → 𝟘≤𝟙 s≡𝕤 ∘→ Trivialᵐ→¬𝟘ᵐ-allowed)

opaque

  -- Another usage rule for erased.

  ▸erased :
    γ ▸[ 𝟘ᵐ[ ok ] ] t →
    (s ≡ 𝕨 → ∃ λ δ → δ ▸[ 𝟘ᵐ[ ok ] ] A) →
    (s ≡ 𝕨 → Prodrec-allowed 𝟘ᵐ[ ok ] (𝟘 ∧ 𝟙) 𝟘 𝟘) →
    𝟘ᶜ ▸[ 𝟘ᵐ[ ok ] ] erased A t
  ▸erased {ok} ▸t ▸A P-ok =
    ▸-cong 𝟘ᵐ?≡𝟘ᵐ (U.▸erased (𝟘ᵐ-allowed→¬Trivialᵐ ok) (▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ▸t)
      (Σ.map idᶠ (▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ)) ∘→ ▸A)
      (PE.subst (λ m → Prodrec-allowed m (𝟘 ∧ 𝟙) _ _) (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ∘→ P-ok))

opaque

  -- A usage rule for erasedrec.

  ▸erasedrec :
    (s ≡ 𝕤 → ¬ T 𝟘ᵐ-allowed → Trivial) →
    (s ≡ 𝕨 → Prodrec-allowed m 𝟙 𝟘 p) →
    (s ≡ 𝕨 → Unitrec-allowed m 𝟙 p) →
    (s ≡ 𝕨 → ∃ λ γ → γ ∙ ⌜ 𝟘ᵐ? ⌝ · p ▸[ 𝟘ᵐ? ] B) →
    δ ∙ 𝟘 ▸[ m ] t →
    η ▸[ m ᵐ· is-𝕨 ] u →
    δ +ᶜ η ▸[ m ] erasedrec p B t u
  ▸erasedrec trivial =
    U.▸erasedrec (λ s≡𝕤 → trivial s≡𝕤 ∘→ Trivialᵐ→¬𝟘ᵐ-allowed)

opaque

  -- A usage rule for mapᴱ.

  ▸mapᴱ′ :
    (s ≡ 𝕨 → ¬ T 𝟘ᵐ-allowed → Trivial) →
    (s ≡ 𝕨 → Prodrec-allowed 𝟘ᵐ? (𝟘 ∧ 𝟙) 𝟘 𝟘) →
    (s ≡ 𝕤 → ¬ T 𝟘ᵐ-allowed → 𝟘 ≤ 𝟙) →
    (s ≡ 𝕨 → ∃ λ γ₁ → γ₁ ▸[ 𝟘ᵐ? ] A) →
    γ₂ ∙ ⌜ 𝟘ᵐ? ⌝ · p ▸[ 𝟘ᵐ? ] t →
    γ₃ ▸[ 𝟘ᵐ? ] u →
    𝟘ᶜ ▸[ m ] mapᴱ A t u
  ▸mapᴱ′ trivial P-ok 𝟘≤𝟙 =
    U.▸mapᴱ′ (λ s≡𝕨 → trivial s≡𝕨 ∘→ Trivialᵐ→¬𝟘ᵐ-allowed)
      P-ok (λ s≡𝕤 → 𝟘≤𝟙 s≡𝕤 ∘→ Trivialᵐ→¬𝟘ᵐ-allowed)

opaque

  -- Another usage rule for mapᴱ.

  ▸mapᴱ :
    (s ≡ 𝕨 → Prodrec-allowed 𝟘ᵐ[ ok ] (𝟘 ∧ 𝟙) 𝟘 𝟘) →
    (s ≡ 𝕨 → ∃ λ γ₁ → γ₁ ▸[ 𝟘ᵐ[ ok ] ] A) →
    γ₂ ∙ 𝟘 ▸[ 𝟘ᵐ[ ok ] ] t →
    γ₃ ▸[ 𝟘ᵐ[ ok ] ] u →
    𝟘ᶜ ▸[ m ] mapᴱ A t u
  ▸mapᴱ {ok} P-ok ▸A ▸t ▸u =
    U.▸mapᴱ (𝟘ᵐ-allowed→¬Trivialᵐ ok)
      (PE.subst (λ m → Prodrec-allowed m (𝟘 ∧ 𝟙) _ _) (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ∘→ P-ok)
      (Σ.map idᶠ (▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ)) ∘→ ▸A)
      (▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ▸t) (▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ▸u)

opaque
  unfolding substᵉ

  -- A usage rule for substᵉ.

  ▸substᵉ :
    (s ≡ 𝕨 → ¬ T 𝟘ᵐ-allowed → Trivial) →
    (s ≡ 𝕨 → Prodrec-allowed 𝟘ᵐ? (𝟘 ∧ 𝟙) 𝟘 𝟘) →
    (s ≡ 𝕤 → ¬ T 𝟘ᵐ-allowed → 𝟘 ≤ 𝟙) →
    []-cong-allowed-mode s m →
    γ₁ ▸[ 𝟘ᵐ? ] A →
    γ₂ ∙ 𝟘 ▸[ m ] B →
    γ₃ ▸[ 𝟘ᵐ? ] t →
    γ₄ ▸[ 𝟘ᵐ? ] u →
    γ₅ ▸[ 𝟘ᵐ? ] v →
    γ₆ ▸[ m ] w →
    ω ·ᶜ (γ₂ +ᶜ γ₆) ▸[ m ] substᵉ A B t u v w
  ▸substᵉ trivial P-ok 𝟘≤𝟙 =
    U.▸substᵉ (λ s≡𝕨 → trivial s≡𝕨 ∘→ Trivialᵐ→¬𝟘ᵐ-allowed)
      P-ok (λ s≡𝕤 → 𝟘≤𝟙 s≡𝕤 ∘→ Trivialᵐ→¬𝟘ᵐ-allowed)

opaque
  unfolding Jᵉ

  -- A usage rule for Jᵉ.

  ▸Jᵉ :
    (s ≡ 𝕨 → ¬ T 𝟘ᵐ-allowed → Trivial) →
    (s ≡ 𝕨 → Prodrec-allowed 𝟘ᵐ? (𝟘 ∧ 𝟙) 𝟘 𝟘) →
    (s ≡ 𝕤 → ¬ T 𝟘ᵐ-allowed → 𝟘 ≤ 𝟙) →
    []-cong-allowed-mode s m →
    γ₁ ▸[ 𝟘ᵐ? ] A →
    γ₂ ▸[ 𝟘ᵐ? ] t →
    γ₃ ∙ 𝟘 ∙ 𝟘 ▸[ m ] B →
    γ₄ ▸[ m ] u →
    γ₅ ▸[ 𝟘ᵐ? ] v →
    γ₆ ▸[ 𝟘ᵐ? ] w →
    ω ·ᶜ (γ₃ +ᶜ γ₄) ▸[ m ] Jᵉ A t B u v w
  ▸Jᵉ trivial P-ok 𝟘≤𝟙 =
    U.▸Jᵉ (λ s≡𝕨 → trivial s≡𝕨 ∘→ Trivialᵐ→¬𝟘ᵐ-allowed)
      P-ok λ s≡𝕤 → 𝟘≤𝟙 s≡𝕤 ∘→ Trivialᵐ→¬𝟘ᵐ-allowed

------------------------------------------------------------------------
-- Inversion lemmas for usage

opaque
  unfolding erased

  -- An inversion lemma for erased.

  inv-usage-erased :
    γ ▸[ m ] erased A t →
    𝟘ᶜ ▸[ 𝟘ᵐ[ ok ] ] t ×
    γ ≤ᶜ 𝟘ᶜ ×
    m ≡ 𝟘ᵐ[ ok ] ×
    (s ≡ 𝕨 → 𝟘ᶜ ▸[ 𝟘ᵐ[ ok ] ] A × Prodrec-allowed m (𝟘 ∧ 𝟙) 𝟘 𝟘)
  inv-usage-erased {ok} ▸erased =
    let ▸t , γ≤ , m≡𝟘ᵐ , prop = U.inv-usage-erased (𝟘ᵐ-allowed→¬Trivialᵐ ok) ▸erased
    in  ▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸t , γ≤ , (case PE.singleton s of λ where
          (𝕤 , PE.refl) → PE.trans (m≡𝟘ᵐ _≡_.refl) 𝟘ᵐ?≡𝟘ᵐ , λ ()
          (𝕨 , PE.refl) → let
            𝟘≤m , ▸A , P-ok = prop PE.refl
            in  lemma _ 𝟘≤m , λ _ → ▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸A , P-ok)
    where
    lemma : ∀ m → 𝟘 ≤ ⌜ m ⌝ → m ≡ 𝟘ᵐ[ ok ]
    lemma 𝟘ᵐ _ = 𝟘ᵐ-cong
    lemma 𝟙ᵐ 𝟘≤𝟙 = ⊥-elim (𝟘≰𝟙 ⦃ 𝟘-well-behaved ok ⦄ 𝟘≤𝟙)
