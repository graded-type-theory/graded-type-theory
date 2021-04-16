{-# OPTIONS --without-K --allow-unsolved-metas #-}

open import Tools.Relation
open import Definition.Modality

module Definition.Modality.Usage.Weakening
  {M : Set} {_≈_ : Rel M _}
  (𝕄 : Modality M _≈_)
  where

open import Definition.Modality.Context 𝕄
open import Definition.Modality.Context.Properties 𝕄
open import Definition.Modality.Properties 𝕄
open import Definition.Modality.Usage 𝕄
open import Definition.Untyped M _≈_ hiding (_∙_)

open import Tools.Fin
open import Tools.Nat renaming (_+_ to _+ⁿ_)
open import Tools.Product
open import Tools.PropositionalEquality as PE

open Modality 𝕄

private
  variable
    ℓ n : Nat

-- Usage of lifted wk1 terms
-- If γ ▸ t, then insertAt ℓ γ 𝟘 ▸ wk (liftn (step id) ℓ) t

liftn-usage : (ℓ : Nat) {γ : Conₘ (ℓ +ⁿ n)} {t : Term (ℓ +ⁿ n)}
            → γ ▸ t → insertAt ℓ γ 𝟘 ▸ wk (liftn (step id) ℓ) t

liftn-usage ℓ Uₘ = PE.subst (_▸ U) (sym (insertAt-𝟘 ℓ)) Uₘ
liftn-usage ℓ ℕₘ = PE.subst (_▸ ℕ) (sym (insertAt-𝟘 ℓ)) ℕₘ
liftn-usage ℓ Emptyₘ = PE.subst (_▸ Empty) (sym (insertAt-𝟘 ℓ)) Emptyₘ
liftn-usage ℓ Unitₘ = PE.subst (_▸ Unit) (sym (insertAt-𝟘 ℓ)) Unitₘ

liftn-usage ℓ (Πₘ γ▸F δ▸G) = sub
  (Πₘ (liftn-usage ℓ γ▸F) (liftn-usage (1+ ℓ) δ▸G))
  (≤ᶜ-reflexive (insertAt-distrib-+ᶜ-𝟘 ℓ _ _))

liftn-usage ℓ (Σₘ γ▸F δ▸G) = sub
  (Σₘ (liftn-usage ℓ γ▸F) (liftn-usage (1+ ℓ) δ▸G))
  (≤ᶜ-reflexive (insertAt-distrib-+ᶜ-𝟘 ℓ _ _))

liftn-usage Nat.zero (var)       = var
liftn-usage (1+ ℓ) (var {x0})   = PE.subst (_▸ (var x0))
  (cong₂ _∙_ (PE.sym (insertAt-𝟘 ℓ)) refl)
  var
liftn-usage (1+ ℓ) (var {x +1}) = subst₂ _▸_
  (cong₂ _∙_ (insertAt-liftn ℓ x) refl)
  refl
  var

liftn-usage ℓ (lamₘ γ▸t) = (lamₘ (liftn-usage (1+ ℓ) γ▸t))

liftn-usage ℓ (_∘ₘ_ {γ = γ} {δ = δ} {p = p} γ▸t δ▸u) =
  sub ((liftn-usage ℓ γ▸t) ∘ₘ (liftn-usage ℓ δ▸u)) eq
  where
  open import Tools.Reasoning.PartialOrder ≤ᶜ-poset
  eq = begin
    insertAt ℓ (γ +ᶜ p ·ᶜ δ) 𝟘               ≈⟨ insertAt-distrib-+ᶜ-𝟘 ℓ γ (p ·ᶜ δ) ⟩
    insertAt ℓ γ 𝟘 +ᶜ insertAt ℓ (p ·ᶜ δ) 𝟘 ≈⟨ +ᶜ-cong ≈ᶜ-refl (insertAt-distrib-·ᶜ-𝟘 ℓ p δ) ⟩
    insertAt ℓ γ 𝟘 +ᶜ p ·ᶜ insertAt ℓ δ 𝟘   ∎

liftn-usage ℓ (prodₘ! γ▸t δ▸u) = sub
  (prodₘ! (liftn-usage ℓ γ▸t) (liftn-usage ℓ δ▸u))
  (≤ᶜ-reflexive (insertAt-distrib-+ᶜ-𝟘 ℓ _ _))

liftn-usage ℓ (fstₘ γ▸t) = subst₂ _▸_
  (PE.sym (insertAt-𝟘 ℓ))
  refl
  (fstₘ (subst₂ _▸_ (insertAt-𝟘 ℓ) refl (liftn-usage ℓ γ▸t)))

liftn-usage ℓ (sndₘ γ▸t) =  subst₂ _▸_
  (PE.sym (insertAt-𝟘 ℓ))
  refl
  (sndₘ (subst₂ _▸_ (insertAt-𝟘 ℓ) refl (liftn-usage ℓ γ▸t)))

liftn-usage ℓ (prodrecₘ {γ = γ} {δ = δ} {p = p} γ▸t δ▸u) = sub
  (prodrecₘ (liftn-usage ℓ γ▸t) (liftn-usage (1+ (1+ ℓ)) δ▸u))
  eq
  where
  open import Tools.Reasoning.PartialOrder ≤ᶜ-poset
  eq = begin
    insertAt ℓ (p ·ᶜ γ +ᶜ δ) 𝟘               ≈⟨ insertAt-distrib-+ᶜ-𝟘 ℓ (p ·ᶜ γ) δ ⟩
    insertAt ℓ (p ·ᶜ γ) 𝟘 +ᶜ insertAt ℓ δ 𝟘 ≈⟨ +ᶜ-cong (insertAt-distrib-·ᶜ-𝟘 ℓ p γ) ≈ᶜ-refl ⟩
    p ·ᶜ insertAt ℓ γ 𝟘 +ᶜ insertAt ℓ δ 𝟘   ∎

liftn-usage ℓ zeroₘ      = PE.subst (_▸ zero) (PE.sym (insertAt-𝟘 ℓ)) zeroₘ
liftn-usage ℓ (sucₘ γ▸t) = sucₘ (liftn-usage ℓ γ▸t)

liftn-usage ℓ (natrecₘ {γ = γ} {δ = δ} {p = p} {r = r} {η = η} γ▸z δ▸s η▸n) = sub
  (natrecₘ (liftn-usage ℓ γ▸z) (liftn-usage (1+ (1+ ℓ)) δ▸s) (liftn-usage ℓ η▸n))
  {!!}
  -- (natrecₘ (liftn-usage ℓ γ▸z) (liftn-usage (1+ (1+ ℓ)) γ▸s) (liftn-usage ℓ δ▸n) r≤0)
  -- (≤ᶜ-reflexive (≈ᶜ-trans (insertAt-distrib-·ᶜ-𝟘 ℓ (r *) (γ +ᶜ p ·ᶜ δ)) (·ᶜ-cong ≈-refl eq)))
  where
  open import Tools.Reasoning.PartialOrder ≤ᶜ-poset
  eq = begin
    insertAt ℓ (nrᶜ (δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ γ) (δ +ᶜ p ·ᶜ η) r) 𝟘 ≈⟨ {!insertAt-distrib-nrᶜ!} ⟩
    nrᶜ (insertAt ℓ (δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ γ) 𝟘) (insertAt ℓ (δ +ᶜ p ·ᶜ η) 𝟘) r ≈⟨ ? ⟩
    nrᶜ (insertAt ℓ δ 𝟘 +ᶜ p ·ᶜ insertAt ℓ η 𝟘 +ᶜ r ·ᶜ insertAt ℓ γ 𝟘)
      (insertAt ℓ δ 𝟘 +ᶜ p ·ᶜ insertAt ℓ η 𝟘) r ∎
  -- begin
  --   insertAt ℓ (γ +ᶜ p ·ᶜ δ) 𝟘               ≈⟨ insertAt-distrib-+ᶜ-𝟘 ℓ γ (p ·ᶜ δ) ⟩
  --   insertAt ℓ γ 𝟘 +ᶜ insertAt ℓ (p ·ᶜ δ) 𝟘 ≈⟨ +ᶜ-cong ≈ᶜ-refl (insertAt-distrib-·ᶜ-𝟘 ℓ p δ) ⟩
  --   insertAt ℓ γ 𝟘 +ᶜ p ·ᶜ insertAt ℓ δ 𝟘   ∎

liftn-usage ℓ (Emptyrecₘ γ▸t) = Emptyrecₘ (liftn-usage ℓ γ▸t)
liftn-usage ℓ starₘ           =  PE.subst (_▸ star) (PE.sym (insertAt-𝟘 ℓ)) starₘ

liftn-usage ℓ (sub γ▸t x) = sub (liftn-usage ℓ γ▸t)
  (insertAt-monotone ℓ _ _ _ _ x ≤-refl)


-- Usage of single lift
-- If γ ▸ t, then insertAt 1 γ 𝟘 ▸ wk (lift (step id)) t

lift-usage : {γ : Conₘ (1+ n)} {t : Term (1+ n)} → γ ▸ t → insertAt 1 γ 𝟘 ▸ wk (lift (step id)) t
lift-usage = liftn-usage 1


-- Usage of wk1
-- If γ ▸ t, then γ ∙ 𝟘 ▸ wk1 t

wk1-usage : {γ : Conₘ n} {t : Term n} → γ ▸ t →  γ ∙ 𝟘 ▸ wk1 t
wk1-usage = liftn-usage 0
