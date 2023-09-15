------------------------------------------------------------------------
-- Properties of the usage relation that hold when zero is well behaved.
------------------------------------------------------------------------

import Graded.Modality
open import Graded.Usage.Restrictions

module Graded.Usage.Properties.Has-well-behaved-zero
  {a} {M : Set a}
  (open Graded.Modality M)
  (𝕄 : Modality)
  (R : Usage-restrictions M)
  (open Modality 𝕄)
  (𝟘-well-behaved : Has-well-behaved-zero semiring-with-meet)
  where

open import Definition.Untyped M using (var)

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Modality.Nr-instances
open import Graded.Mode 𝕄
open import Graded.Usage 𝕄 R
open import Graded.Usage.Inversion 𝕄 R
open import Graded.Modality.Properties.Has-well-behaved-zero
            semiring-with-meet 𝟘-well-behaved

open import Tools.Bool using (T)
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Sum

private
  variable
    γ δ η : Conₘ _
    x : Fin _
    p q r : M


-- A well-resourced variable under mode 𝟙ᵐ is not associated with
-- grade 𝟘.
--
-- Proof by induction on the variable (de Bruijn index).

valid-var-usage : γ ▸[ 𝟙ᵐ ] var x → γ ⟨ x ⟩ ≢ 𝟘
valid-var-usage γ▸x γ⟨x⟩≡𝟘 = 𝟘≰𝟙 (lemma _ (inv-usage-var γ▸x) γ⟨x⟩≡𝟘)
  where
  lemma : ∀ x → γ ≤ᶜ 𝟘ᶜ , x ≔ 𝟙 → γ ⟨ x ⟩ ≡ 𝟘 → 𝟘 ≤ 𝟙
  lemma x0 (_ ∙ γ⟨x⟩≤𝟙) refl = γ⟨x⟩≤𝟙
  lemma (x +1) (γ≤eᵢ ∙ _) γ⟨x⟩≡𝟘 = lemma x γ≤eᵢ γ⟨x⟩≡𝟘

-- A variant of the positivity property for addition for the
-- usage relation for variables.

x◂𝟘∈γ+δˡ : p ≡ 𝟘 → x ◂ p ∈ γ +ᶜ δ → x ◂ 𝟘 ∈ γ
x◂𝟘∈γ+δˡ {x = ()} {ε} _
x◂𝟘∈γ+δˡ {x = x0} {γ ∙ p} {δ ∙ q} p+q≡𝟘 here =
  subst (λ x → x0 ◂ x ∈ (γ ∙ p)) (+-positiveˡ p+q≡𝟘) here
x◂𝟘∈γ+δˡ {x = x +1} {γ ∙ p} {δ ∙ q} eq (there d) = there (x◂𝟘∈γ+δˡ eq d)

-- A variant of the positivity property for addition for the
-- usage relation for variables.

x◂𝟘∈γ+δʳ : p ≡ 𝟘 → x ◂ p ∈ γ +ᶜ δ → x ◂ 𝟘 ∈ δ
x◂𝟘∈γ+δʳ {γ = γ} {δ} p≡𝟘 d =
  x◂𝟘∈γ+δˡ p≡𝟘 (subst (λ x → _ ◂ _ ∈ x) (≈ᶜ→≡ (+ᶜ-comm γ δ)) d)

-- A variant of the zero-product property for the
-- usage relation for variables.

x◂𝟘∈pγ : q ≡ 𝟘 → p ≢ 𝟘 → x ◂ q ∈ p ·ᶜ γ → x ◂ 𝟘 ∈ γ
x◂𝟘∈pγ {x = ()} {ε} q≡𝟘 p≢𝟘 d
x◂𝟘∈pγ {x = x0} {γ ∙ r} pr≡𝟘 p≢𝟘 here = case zero-product pr≡𝟘 of λ where
  (inj₁ p≡𝟘) → ⊥-elim (p≢𝟘 p≡𝟘)
  (inj₂ refl) → here
x◂𝟘∈pγ {x = x +1} {γ ∙ r} q≡𝟘 p≢𝟘 (there d) =
  there (x◂𝟘∈pγ q≡𝟘 p≢𝟘 d)

-- A variant of the positivity property for meet for the
-- usage relation for variables.

x◂𝟘∈γ∧δˡ : p ≡ 𝟘 → x ◂ p ∈ γ ∧ᶜ δ → x ◂ 𝟘 ∈ γ
x◂𝟘∈γ∧δˡ {x = ()} {ε} _
x◂𝟘∈γ∧δˡ {x = x0} {γ ∙ p} {δ ∙ q} p∧q≡𝟘 here =
  subst (λ x → x0 ◂ x ∈ (γ ∙ p)) (∧-positiveˡ p∧q≡𝟘) here
x◂𝟘∈γ∧δˡ {x = x +1} {γ ∙ p} {δ ∙ q} eq (there d) =
  there (x◂𝟘∈γ∧δˡ eq d)

-- A variant of the positivity property for meet for the
-- usage relation for variables.

x◂𝟘∈γ∧δʳ : p ≡ 𝟘 → x ◂ p ∈ γ ∧ᶜ δ → x ◂ 𝟘 ∈ δ
x◂𝟘∈γ∧δʳ {γ = γ} {δ} p≡𝟘 d =
  x◂𝟘∈γ∧δˡ p≡𝟘 (subst (λ x → _ ◂ _ ∈ x) (≈ᶜ→≡ (∧ᶜ-comm γ δ)) d)

-- A variant of the positivity property for ⊛ᵣ for the
-- usage relation for variables.

x◂𝟘∈γ⊛δˡ :
  ⦃ has-star : Has-star semiring-with-meet ⦄ →
  p ≡ 𝟘 → x ◂ p ∈ γ ⊛ᶜ δ ▷ r → x ◂ 𝟘 ∈ γ
x◂𝟘∈γ⊛δˡ {x = x0} {γ ∙ p} {δ ∙ q} p⊛q≡𝟘 here =
  subst (λ x → _ ◂ x ∈ γ ∙ p) (⊛≡𝟘ˡ p⊛q≡𝟘) here
x◂𝟘∈γ⊛δˡ {x = x +1} {γ ∙ p} {δ ∙ q} eq (there d) =
  there (x◂𝟘∈γ⊛δˡ eq d)

-- A variant of the positivity property for ⊛ᵣ for the
-- usage relation for variables.

x◂𝟘∈γ⊛δʳ :
  ⦃ has-star : Has-star semiring-with-meet ⦄ →
  p ≡ 𝟘 → x ◂ p ∈ γ ⊛ᶜ δ ▷ r → x ◂ 𝟘 ∈ δ
x◂𝟘∈γ⊛δʳ {x = x0} {γ ∙ p} {δ ∙ q} p⊛q≡𝟘 here =
  subst (λ x → _ ◂ x ∈ δ ∙ q) (⊛≡𝟘ʳ p⊛q≡𝟘) here
x◂𝟘∈γ⊛δʳ {x = x +1} {γ ∙ p} {δ ∙ q} eq (there d) =
  there (x◂𝟘∈γ⊛δʳ eq d)

-- A kind of positivity property for nrᶜ and _◂_∈_.

◂𝟘∈nrᶜ₁ :
  ⦃ has-nr : Has-nr semiring-with-meet ⦄ →
  q ≡ 𝟘 → x ◂ q ∈ nrᶜ p r γ δ η → x ◂ 𝟘 ∈ γ
◂𝟘∈nrᶜ₁ {x = x0} {γ = _ ∙ _} {δ = _ ∙ _} {η = _ ∙ _} nrᶜ≡𝟘 here =
  subst (_ ◂_∈ _) (nr-positive 𝟘-well-behaved nrᶜ≡𝟘 .proj₁) here
◂𝟘∈nrᶜ₁ {x = _ +1} {γ = _ ∙ _} {δ = _ ∙ _} {η = _ ∙ _} eq (there p) =
  there (◂𝟘∈nrᶜ₁ eq p)

-- A kind of positivity property for nrᶜ and _◂_∈_.

◂𝟘∈nrᶜ₂ :
  ⦃ has-nr : Has-nr semiring-with-meet ⦄ →
  q ≡ 𝟘 → x ◂ q ∈ nrᶜ p r γ δ η → x ◂ 𝟘 ∈ δ
◂𝟘∈nrᶜ₂ {x = x0} {γ = _ ∙ _} {δ = _ ∙ _} {η = _ ∙ _} nrᶜ≡𝟘 here =
  subst (_ ◂_∈ _) (nr-positive 𝟘-well-behaved nrᶜ≡𝟘 .proj₂ .proj₁) here
◂𝟘∈nrᶜ₂ {x = _ +1} {γ = _ ∙ _} {δ = _ ∙ _} {η = _ ∙ _} eq (there p) =
  there (◂𝟘∈nrᶜ₂ eq p)

-- A kind of positivity property for nrᶜ and _◂_∈_.

◂𝟘∈nrᶜ₃ :
  ⦃ has-nr : Has-nr semiring-with-meet ⦄ →
  q ≡ 𝟘 → x ◂ q ∈ nrᶜ p r γ δ η → x ◂ 𝟘 ∈ η
◂𝟘∈nrᶜ₃ {x = x0} {γ = _ ∙ _} {δ = _ ∙ _} {η = _ ∙ _} nrᶜ≡𝟘 here =
  subst (_ ◂_∈ _) (nr-positive 𝟘-well-behaved nrᶜ≡𝟘 .proj₂ .proj₂) here
◂𝟘∈nrᶜ₃ {x = _ +1} {γ = _ ∙ _} {δ = _ ∙ _} {η = _ ∙ _} eq (there p) =
  there (◂𝟘∈nrᶜ₃ eq p)

-- A variant of the property that nothing is smaller than 𝟘 for the
-- usage relation for variables.

x◂𝟘∈γ≤δ : x ◂ 𝟘 ∈ γ → γ ≤ᶜ δ → x ◂ 𝟘 ∈ δ
x◂𝟘∈γ≤δ {δ = δ ∙ p} here (γ≤δ ∙ 𝟘≤p) rewrite 𝟘≮ 𝟘≤p = here
x◂𝟘∈γ≤δ {δ = δ ∙ p} (there d) (γ≤δ ∙ _) = there (x◂𝟘∈γ≤δ d γ≤δ)
