{-#OPTIONS --without-K --allow-unsolved-metas #-}
module Definition.Modality.Usage.Weakening where

open import Definition.Modality
open import Definition.Modality.Context
open import Definition.Modality.Context.Properties
open import Definition.Modality.Properties
open import Definition.Modality.Usage
open import Definition.Untyped

open import Tools.Fin
open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality as PE

private
  variable
    M : Set
    ℓ n : Nat

-- Usage of lifted wk1 terms
-- If γ ▸ t, then insertAt ℓ γ 𝟘 ▸ wk (liftn (step id) ℓ) t

liftn-usage : {𝕄 : Modality M} (ℓ : Nat) {γ : Conₘ 𝕄 (ℓ + n)} {t : Term M (ℓ + n)}
            → γ ▸ t → insertAt ℓ γ (Modality.𝟘 𝕄) ▸ wk (liftn (step id) ℓ) t

liftn-usage ℓ Uₘ = PE.subst (_▸ U) (sym (insertAt-𝟘 ℓ)) Uₘ
liftn-usage ℓ ℕₘ = PE.subst (_▸ ℕ) (sym (insertAt-𝟘 ℓ)) ℕₘ
liftn-usage ℓ Emptyₘ = PE.subst (_▸ Empty) (sym (insertAt-𝟘 ℓ)) Emptyₘ
liftn-usage ℓ Unitₘ = PE.subst (_▸ Unit) (sym (insertAt-𝟘 ℓ)) Unitₘ

liftn-usage {𝕄 = 𝕄} ℓ (Πₘ γ▸F δ▸G) = subst₂ _▸_
  ( PE.sym (insertAt-distrib-+ᶜ-𝟘 ℓ _ _) )
  refl
  (Πₘ (liftn-usage ℓ γ▸F) (liftn-usage (1+ ℓ) δ▸G))

liftn-usage ℓ (Σₘ γ▸F δ▸G) = subst₂ _▸_
  (PE.sym (insertAt-distrib-+ᶜ-𝟘 ℓ _ _))
  refl
  (Σₘ (liftn-usage ℓ γ▸F) (liftn-usage (1+ ℓ) δ▸G))

liftn-usage Nat.zero (var)       = var
liftn-usage (1+ ℓ) (var {x0})   = PE.subst (_▸ (var x0))
  (cong₂ _∙_ (PE.sym (insertAt-𝟘 ℓ)) refl)
  var
liftn-usage (1+ ℓ) (var {x +1}) = subst₂ _▸_
  (cong₂ _∙_ (insertAt-liftn ℓ x) refl)
  refl
  var

liftn-usage ℓ (lamₘ γ▸t) = (lamₘ (liftn-usage (1+ ℓ) γ▸t))

liftn-usage {𝕄 = 𝕄} ℓ (_∘ₘ_ {δ = δ} γ▸t δ▸u) = subst₂ _▸_ eq refl ((
  liftn-usage ℓ γ▸t) ∘ₘ (liftn-usage ℓ δ▸u))
  where
  eq = begin
     _ ≡⟨ cong₂ _+ᶜ_ refl (PE.sym (insertAt-distrib-·ᶜ ℓ _ δ _ _)) ⟩
     _ ≡⟨ cong₂ _+ᶜ_ refl (cong (insertAt ℓ _) (proj₂ (Modality.·-Zero 𝕄) _)) ⟩
     _ ≡⟨ PE.sym (insertAt-distrib-+ᶜ-𝟘 ℓ _ _) ⟩
     _ ∎

liftn-usage ℓ (prodₘ! γ▸t δ▸u) = subst₂ _▸_
  (PE.sym (insertAt-distrib-+ᶜ-𝟘 ℓ _ _))
  refl
  (prodₘ! (liftn-usage ℓ γ▸t) (liftn-usage ℓ δ▸u))

liftn-usage ℓ (fstₘ γ▸t) = subst₂ _▸_
  (PE.sym (insertAt-𝟘 ℓ))
  refl
  (fstₘ (subst₂ _▸_ (insertAt-𝟘 ℓ) refl (liftn-usage ℓ γ▸t)))

liftn-usage ℓ (sndₘ γ▸t) =  subst₂ _▸_
  (PE.sym (insertAt-𝟘 ℓ))
  refl
  (sndₘ (subst₂ _▸_ (insertAt-𝟘 ℓ) refl (liftn-usage ℓ γ▸t)))

liftn-usage {𝕄 = 𝕄} ℓ (prodrecₘ {δ = δ} γ▸t δ▸u) = subst₂ _▸_ eq refl
  (prodrecₘ (liftn-usage ℓ γ▸t) (liftn-usage (1+ (1+ ℓ)) δ▸u))
  where
  eq = begin
     _ ≡⟨ cong₂ _+ᶜ_ (PE.sym (insertAt-distrib-·ᶜ {𝕄 = 𝕄} ℓ _ δ _ _)) refl ⟩
     _ ≡⟨ cong₂ _+ᶜ_ (cong (insertAt ℓ _) (proj₂ (Modality.·-Zero 𝕄) _)) refl ⟩
     _ ≡⟨ PE.sym (insertAt-distrib-+ᶜ ℓ _ _ _ _) ⟩
     _ ≡⟨ cong (insertAt ℓ _) (proj₁ (Modality.+-Identity 𝕄) (Modality.𝟘 𝕄)) ⟩
     _ ∎

liftn-usage ℓ zeroₘ      = PE.subst (_▸ zero) (PE.sym (insertAt-𝟘 ℓ)) zeroₘ
liftn-usage ℓ (sucₘ γ▸t) = sucₘ (liftn-usage ℓ γ▸t)

liftn-usage {𝕄 = 𝕄} ℓ (natrecₘ {δ = δ} γ▸z γ▸s δ▸n X≤γ′) = {!!}
-- subst₂ _▸_ eq refl
--   (natrecₘ (liftn-usage ℓ γ▸z) (liftn-usage (1+ (1+ ℓ)) γ▸s) (liftn-usage ℓ δ▸n) r≤0)
--   where
--   eq = begin
--     _ ≡⟨ cong₂ _·ᶜ_ refl (cong₂ _+ᶜ_ refl (sym (insertAt-distrib-·ᶜ ℓ _ δ _ _))) ⟩
--     _ ≡⟨ cong₂ _·ᶜ_ refl (cong₂ _+ᶜ_ refl (cong (insertAt ℓ _) (proj₂ (Modality.·-Zero 𝕄) _))) ⟩
--     _ ≡⟨ cong₂ _·ᶜ_ refl (sym (insertAt-distrib-+ᶜ ℓ _ _ _ _)) ⟩
--     _ ≡⟨ cong₂ _·ᶜ_ refl (cong (insertAt ℓ _) (proj₁ (Modality.+-Identity 𝕄) _)) ⟩
--     _ ≡⟨ sym (insertAt-distrib-·ᶜ ℓ _ δ _ _) ⟩
--     _ ≡⟨ cong (insertAt ℓ _) (proj₂ (Modality.·-Zero 𝕄) _) ⟩
--     _ ∎

liftn-usage ℓ (Emptyrecₘ γ▸t) = Emptyrecₘ (liftn-usage ℓ γ▸t)
liftn-usage ℓ starₘ           =  PE.subst (_▸ star) (PE.sym (insertAt-𝟘 ℓ)) starₘ

liftn-usage {𝕄 = 𝕄} ℓ (sub γ▸t x) = sub (liftn-usage ℓ γ▸t)
  (insertAt-monotone ℓ _ _ _ _ x (≤-reflexive {𝕄 = 𝕄}))


-- Usage of single lift
-- If γ ▸ t, then insertAt 1 γ 𝟘 ▸ wk (lift (step id)) t

lift-usage : {𝕄 : Modality M} {γ : Conₘ 𝕄 (1+ n)} {t : Term M (1+ n)}
            → γ ▸ t → insertAt 1 γ (Modality.𝟘 𝕄) ▸ wk (lift (step id)) t
lift-usage = liftn-usage 1


-- Usage of wk1
-- If γ ▸ t, then γ ∙ 𝟘 ▸ wk1 t

wk1-usage : {𝕄 : Modality M} {γ : Conₘ 𝕄 n} {t : Term M n}
            → γ ▸ t →  γ ∙ (Modality.𝟘 𝕄) ▸ wk1 t
wk1-usage = liftn-usage 0
