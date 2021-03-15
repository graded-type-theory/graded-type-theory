{-# OPTIONS --without-K --safe #-}
module Definition.Modality.Usage.Properties where

open import Definition.Modality
open import Definition.Modality.Context
open import Definition.Modality.Context.Properties
open import Definition.Modality.Properties
open import Definition.Modality.Usage
open import Definition.Untyped as U hiding (_∷_)
open import Definition.Typed

open import Tools.Fin
open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality as PE


private
  variable
    n : Nat
    M : Set
    𝕄 : Modality M
    Γ : Con (Term M) n
    t u A : Term M n
    γ γ′ δ η : Conₘ 𝕄 n
    p : M

usage-upper-bound : γ ▸ t → γ ≤ᶜ ⌈ t ⌉
usage-upper-bound Uₘ = ≤ᶜ-reflexive
usage-upper-bound ℕₘ = ≤ᶜ-reflexive
usage-upper-bound Emptyₘ = ≤ᶜ-reflexive
usage-upper-bound Unitₘ = ≤ᶜ-reflexive
usage-upper-bound (Πₘ {δ = δ} {q} {G₁} F G) = +ᶜ-monotone₂
  (usage-upper-bound F)
  (PE.subst (δ ≡_) (tail-linear∧ {γ = δ ∙ q} {⌈ G₁ ⌉})
            (cong tailₘ (usage-upper-bound G)))
usage-upper-bound (Σₘ {δ = δ} {q} {G₁} F G) = +ᶜ-monotone₂
  (usage-upper-bound F)
  (PE.subst (δ ≡_) (tail-linear∧ {γ = δ ∙ q} {⌈ G₁ ⌉})
                   (cong tailₘ (usage-upper-bound G)))
usage-upper-bound var = ≤ᶜ-reflexive
usage-upper-bound {γ = γ} (lamₘ {p = p} {t₁} t) = PE.subst (γ ≡_)
  (tail-linear∧ {γ = γ ∙ p} {⌈ t₁ ⌉})
  (cong tailₘ (usage-upper-bound t))
usage-upper-bound (t ∘ₘ u) = +ᶜ-monotone₂ (usage-upper-bound t) (·ᶜ-monotone (usage-upper-bound u))
usage-upper-bound (prodₘ! t u) = +ᶜ-monotone₂ (usage-upper-bound t) (usage-upper-bound u)
usage-upper-bound (fstₘ t) = usage-upper-bound t
usage-upper-bound (sndₘ t) = usage-upper-bound t
usage-upper-bound (prodrecₘ {γ} {δ = δ} {p} {u = u₁} t u) = +ᶜ-monotone₂
  (·ᶜ-monotone (usage-upper-bound t))
  (begin
    tailₘ (tailₘ (δ ∙ p ∙ p))            ≡⟨ cong tailₘ (cong tailₘ (usage-upper-bound u)) ⟩
    tailₘ (tailₘ (δ ∙ p ∙ p ∧ᶜ ⌈ u₁ ⌉))  ≡⟨ cong tailₘ (tail-linear∧ {γ = δ ∙ p ∙ p} {⌈ u₁ ⌉}) ⟩
    tailₘ (δ ∙ p ∧ᶜ tailₘ ⌈ u₁ ⌉)        ≡⟨ tail-linear∧ {γ = δ ∙ p} {tailₘ ⌈ u₁ ⌉} ⟩
    δ ∧ᶜ tailₘ (tailₘ ⌈ u₁ ⌉) ∎
  )
usage-upper-bound zeroₘ = ≤ᶜ-reflexive
usage-upper-bound (sucₘ t) = usage-upper-bound t
usage-upper-bound (natrecₘ {γ = γ} {q = q} {p = p} {s = s} x x₁ x₂) = ·ᶜ-monotone (+ᶜ-monotone₂
  (subst₂ _≤ᶜ_ (∧ᶜ-Idempotent γ) refl (∧ᶜ-monotone₂ (usage-upper-bound x) eq))
  (·ᶜ-monotone (usage-upper-bound x₂)))
  where
  eq = begin
         tailₘ (tailₘ (γ ∙ q ∙ p))
           ≡⟨ cong tailₘ (cong tailₘ (usage-upper-bound x₁)) ⟩
         tailₘ (tailₘ (γ ∙ q ∙ p ∧ᶜ ⌈ s ⌉))
           ≡⟨ cong tailₘ (tail-linear∧ {γ = γ ∙ q ∙ p} {⌈ s ⌉}) ⟩
         tailₘ ((γ ∙ q) ∧ᶜ tailₘ ⌈ s ⌉)
           ≡⟨ tail-linear∧ {γ = γ ∙ q} {tailₘ ⌈ s ⌉} ⟩
         γ ∧ᶜ tailₘ (tailₘ ⌈ s ⌉) ∎

usage-upper-bound (Emptyrecₘ e) = usage-upper-bound e
usage-upper-bound starₘ = ≤ᶜ-reflexive
usage-upper-bound (sub t x) = ≤ᶜ-transitive x (usage-upper-bound t)


-- Usage of lifted wk1 terms

liftn-usage : {𝕄 : Modality M} (ℓ : Nat) {γ : Conₘ 𝕄 (ℓ + n)} {t : Term M (ℓ + n)}
            → γ ▸ t → insertAt ℓ γ (Modality.𝟘 𝕄) ▸ wk (liftn (step id) ℓ) t
liftn-usage ℓ Uₘ     = PE.subst (_▸ U) (insertAt-𝟘 ℓ) Uₘ
liftn-usage ℓ ℕₘ     = PE.subst (_▸ ℕ) (insertAt-𝟘 ℓ) ℕₘ
liftn-usage ℓ Emptyₘ = PE.subst (_▸ Empty) (insertAt-𝟘 ℓ) Emptyₘ
liftn-usage ℓ Unitₘ  = PE.subst (_▸ Unit) (insertAt-𝟘 ℓ) Unitₘ

liftn-usage {𝕄 = 𝕄} ℓ (Πₘ γ▸F δ▸G) = subst₂ _▸_
  (insertAt-distrib-+ᶜ-𝟘 ℓ _ _)
  refl
  (Πₘ (liftn-usage ℓ γ▸F) (liftn-usage (1+ ℓ) δ▸G))

liftn-usage ℓ (Σₘ γ▸F δ▸G) = subst₂ _▸_
  (insertAt-distrib-+ᶜ-𝟘 ℓ _ _)
  refl
  (Σₘ (liftn-usage ℓ γ▸F) (liftn-usage (1+ ℓ) δ▸G))

liftn-usage Nat.zero (var)       = var
liftn-usage (1+ ℓ) (var {x0})   = PE.subst (_▸ (var x0))
  (cong₂ _∙_ (insertAt-𝟘 ℓ) refl)
  var
liftn-usage (1+ ℓ) (var {x +1}) = subst₂ _▸_
  (cong₂ _∙_ (insertAt-liftn ℓ x) refl)
  refl
  var

liftn-usage ℓ (lamₘ γ▸t) = (lamₘ (liftn-usage (1+ ℓ) γ▸t))

liftn-usage {𝕄 = 𝕄} ℓ (_∘ₘ_ {δ = δ} γ▸t δ▸u) =
  subst₂ _▸_ eq refl ((liftn-usage ℓ γ▸t) ∘ₘ (liftn-usage ℓ δ▸u))
  where
  eq = begin
    _ ≡⟨ cong₂ _+ᶜ_ refl (insertAt-distrib-·ᶜ {𝕄 = 𝕄} ℓ _ δ _ _) ⟩
    _ ≡⟨ cong₂ _+ᶜ_ refl (cong (insertAt ℓ _) (proj₂ (Modality.·-Zero 𝕄) _)) ⟩
    _ ≡⟨ insertAt-distrib-+ᶜ ℓ _ _ _ _ ⟩
    _ ≡⟨ cong (insertAt ℓ _) (proj₁ (Modality.+-Identity 𝕄) (Modality.𝟘 𝕄)) ⟩
    _ ∎

liftn-usage ℓ (prodₘ! γ▸t δ▸u) = subst₂ _▸_
  (insertAt-distrib-+ᶜ-𝟘 ℓ _ _)
  refl
  (prodₘ! (liftn-usage ℓ γ▸t) (liftn-usage ℓ δ▸u))

liftn-usage ℓ (fstₘ γ▸t) = subst₂ _▸_
  (insertAt-𝟘 ℓ)
  refl
  (fstₘ (subst₂ _▸_ (PE.sym (insertAt-𝟘 ℓ)) refl (liftn-usage ℓ γ▸t)))

liftn-usage ℓ (sndₘ γ▸t) =  subst₂ _▸_
  (insertAt-𝟘 ℓ)
  refl
  (sndₘ (subst₂ _▸_ (PE.sym (insertAt-𝟘 ℓ)) refl (liftn-usage ℓ γ▸t)))

liftn-usage {𝕄 = 𝕄} ℓ (prodrecₘ {δ = δ} γ▸t δ▸u) = subst₂ _▸_ eq refl
  (prodrecₘ (liftn-usage ℓ γ▸t) (liftn-usage (1+ (1+ ℓ)) δ▸u))
  where
  eq = begin
     _ ≡⟨ cong₂ _+ᶜ_ (insertAt-distrib-·ᶜ {𝕄 = 𝕄} ℓ _ δ _ _) refl ⟩
     _ ≡⟨ cong₂ _+ᶜ_ (cong (insertAt ℓ _) (proj₂ (Modality.·-Zero 𝕄) _)) refl ⟩
     _ ≡⟨ insertAt-distrib-+ᶜ ℓ _ _ _ _ ⟩
     _ ≡⟨ cong (insertAt ℓ _) (proj₁ (Modality.+-Identity 𝕄) (Modality.𝟘 𝕄)) ⟩
     _ ∎

liftn-usage ℓ zeroₘ      = PE.subst (_▸ zero) (insertAt-𝟘 ℓ) zeroₘ
liftn-usage ℓ (sucₘ γ▸t) = sucₘ (liftn-usage ℓ γ▸t)

liftn-usage {𝕄 = 𝕄} ℓ (natrecₘ {δ = δ} γ▸z γ▸s δ▸n) = subst₂ _▸_ eq refl
  (natrecₘ (liftn-usage ℓ γ▸z) (liftn-usage (1+ (1+ ℓ)) γ▸s) (liftn-usage ℓ δ▸n))
  where
  eq = begin
     _ ≡⟨ cong₂ _·ᶜ_ refl (cong₂ _+ᶜ_ refl (insertAt-distrib-·ᶜ ℓ _ δ _ _)) ⟩
      _ ≡⟨ cong₂ _·ᶜ_ refl (cong₂ _+ᶜ_ refl (cong (insertAt ℓ _) (proj₂ (Modality.·-Zero 𝕄) _))) ⟩
     _ ≡⟨ cong₂ _·ᶜ_ refl (insertAt-distrib-+ᶜ ℓ _ _ _ _) ⟩
     _ ≡⟨ cong₂ _·ᶜ_ refl (cong (insertAt ℓ _) (proj₁ (Modality.+-Identity 𝕄) (Modality.𝟘 𝕄))) ⟩
     _ ≡⟨ insertAt-distrib-·ᶜ {𝕄 = 𝕄} ℓ _ δ _ _ ⟩
     _ ≡⟨ cong (insertAt ℓ _) (proj₂ (Modality.·-Zero 𝕄) _) ⟩
     _ ∎

liftn-usage ℓ (Emptyrecₘ γ▸t) = Emptyrecₘ (liftn-usage ℓ γ▸t)
liftn-usage ℓ starₘ           =  PE.subst (_▸ star) (insertAt-𝟘 ℓ) starₘ

liftn-usage {𝕄 = 𝕄} ℓ (sub γ▸t x) = sub (liftn-usage ℓ γ▸t)
  (insertAt-monotone ℓ _ _ _ _ x (≤-reflexive {𝕄 = 𝕄}))


-- Usage of single lift

lift-usage : {𝕄 : Modality M} {γ : Conₘ 𝕄 (1+ n)} {t : Term M (1+ n)}
            → γ ▸ t →  insertAt 1 γ (Modality.𝟘 𝕄) ▸ wk (lift (step id)) t
lift-usage = liftn-usage 1


-- Usage of wk1

wk1-usage : {𝕄 : Modality M} {γ : Conₘ 𝕄 n} {t : Term M n}
            → γ ▸ t →  γ ∙ (Modality.𝟘 𝕄) ▸ wk1 t
wk1-usage = liftn-usage 0


-- Inversion lemmata for  γ ▸ t

-- If γ ▸ star then γ ≤ᶜ 𝟘ᶜ

inv-usage-star : γ ▸ star → γ ≤ᶜ 𝟘ᶜ
inv-usage-star starₘ = ≤ᶜ-reflexive
inv-usage-star (sub  δ▸star γ≤δ) = ≤ᶜ-transitive γ≤δ (inv-usage-star δ▸star)

inv-usage-zero : γ ▸ zero → γ ≤ᶜ 𝟘ᶜ
inv-usage-zero zeroₘ = ≤ᶜ-reflexive
inv-usage-zero (sub  δ▸zero γ≤δ) = ≤ᶜ-transitive γ≤δ (inv-usage-zero δ▸zero)

inv-usage-lam : γ ▸ lam p t → ∃ λ δ → γ ≤ᶜ δ × (δ ∙ p) ▸ t
inv-usage-lam (lamₘ γ∙p▸t) = _ , ≤ᶜ-reflexive , γ∙p▸t
inv-usage-lam (sub δ▸λpt γ≤δ) with inv-usage-lam δ▸λpt
... | η , δ≤η , η∙p▸t = η , ≤ᶜ-transitive γ≤δ δ≤η , η∙p▸t

record InvUsageApp {n} {M} {𝕄 : Modality M} (γ : Conₘ 𝕄 n) (t : Term M n) (p : M) (u : Term M n) : Set where
  constructor invUsageApp
  field
    {uf ua}  : Conₘ 𝕄 n
    usageFun : uf ▸ t
    usageArg : ua ▸ u
    usageLeq : γ ≤ᶜ (uf +ᶜ p ·ᶜ ua)

inv-usage-app : γ′ ▸ (t ∘ p ▷ u) → InvUsageApp γ′ t p u
inv-usage-app (γ▸t ∘ₘ δ▸u) = invUsageApp γ▸t δ▸u ≤ᶜ-reflexive
inv-usage-app (sub γ▸t∘p▷u γ′≤γ) with inv-usage-app γ▸t∘p▷u
... | invUsageApp δ▸t η▸u γ≤δ+pη = invUsageApp δ▸t η▸u (≤ᶜ-transitive γ′≤γ γ≤δ+pη)
