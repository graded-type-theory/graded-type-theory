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
    t u A F : Term M n
    G : Term M (1+ n)
    γ γ′ : Conₘ 𝕄 n
    p q : M

-- The contents of two valid modality context can be freely interchanged

Conₘ-interchange : {𝕄 : Modality M} {γ δ : Conₘ 𝕄 n}
            → γ ▸ t → δ ▸ t → (x : Fin n) →
            let p = δ ⟨ x ⟩
            in  (γ , x ≔ p) ▸ t
Conₘ-interchange (sub γ▸t γ≤γ′) δ▸t x  = sub (Conₘ-interchange γ▸t δ▸t x) (update-monotoneˡ x γ≤γ′)
Conₘ-interchange γ▸t (sub γ′▸t δ≤γ′) x = sub (Conₘ-interchange γ▸t γ′▸t x) (update-monotoneʳ x (lookup-monotone x δ≤γ′))
Conₘ-interchange {𝕄 = 𝕄} Uₘ Uₘ x     = subst₂ _▸_ (PE.sym (update-self 𝟘ᶜ x)) refl Uₘ
Conₘ-interchange ℕₘ ℕₘ x               = subst₂ _▸_ (PE.sym (update-self 𝟘ᶜ x)) refl ℕₘ
Conₘ-interchange Emptyₘ Emptyₘ x       = subst₂ _▸_ (PE.sym (update-self 𝟘ᶜ x)) refl Emptyₘ
Conₘ-interchange Unitₘ Unitₘ x         = subst₂ _▸_ (PE.sym (update-self 𝟘ᶜ x)) refl Unitₘ

Conₘ-interchange (Πₘ {γ} {δ = δ} γ▸t γ▸t₁) (Πₘ {γ₁} {δ = δ₁} δ▸t δ▸t₁) x = subst₂ _▸_ eq refl
  (Πₘ (Conₘ-interchange γ▸t δ▸t x) (Conₘ-interchange γ▸t₁ δ▸t₁ (x +1)))
  where
  eq = begin
        (γ , x ≔ (γ₁ ⟨ x ⟩)) +ᶜ (δ , x ≔ (δ₁ ⟨ x ⟩))
          ≡⟨ update-linear-+ᶜ γ δ _ _ x ⟩
        (γ +ᶜ δ) , x ≔ _
          ≡⟨ cong₃ _,_≔_ refl refl (PE.sym (lookup-linear-+ᶜ γ₁ δ₁ x)) ⟩
        ((γ +ᶜ δ) , x ≔ _) ∎

Conₘ-interchange (Σₘ {γ} {δ = δ} γ▸t γ▸t₁) (Σₘ {γ₁} {δ = δ₁} δ▸t δ▸t₁) x = subst₂ _▸_ eq refl
  (Σₘ (Conₘ-interchange γ▸t δ▸t x) (Conₘ-interchange γ▸t₁ δ▸t₁ (x +1)))
  where
  eq = begin
        (γ , x ≔ (γ₁ ⟨ x ⟩)) +ᶜ (δ , x ≔ (δ₁ ⟨ x ⟩))
          ≡⟨ update-linear-+ᶜ γ δ _ _ x ⟩
        (γ +ᶜ δ) , x ≔ _
          ≡⟨ cong₃ _,_≔_ refl refl (PE.sym (lookup-linear-+ᶜ γ₁ δ₁ x)) ⟩
        ((γ +ᶜ δ) , x ≔ _) ∎

Conₘ-interchange {𝕄 = 𝕄} (var {x₁}) var x = subst₂ _▸_
  (PE.sym (update-self (𝟘ᶜ , x₁ ≔ (Modality.𝟙 𝕄)) x)) refl var

Conₘ-interchange (lamₘ γ▸t) (lamₘ δ▸t) x = lamₘ (Conₘ-interchange γ▸t δ▸t (x +1))

Conₘ-interchange {𝕄 = 𝕄} (_∘ₘ_ {γ} {δ = δ} {p = p} γ▸t γ▸t₁) (_∘ₘ_ {γ₁} {δ = δ₁} δ▸t δ▸t₁) x =
  subst₂ _▸_ eq refl ((Conₘ-interchange γ▸t δ▸t x) ∘ₘ (Conₘ-interchange γ▸t₁ δ▸t₁ x))
  where
  eq = begin
       (γ , x ≔ (γ₁ ⟨ x ⟩)) +ᶜ p ·ᶜ (δ , x ≔ (δ₁ ⟨ x ⟩))
         ≡⟨ cong₂ _+ᶜ_ refl (update-linear-·ᶜ δ p _ x) ⟩
       (γ , x ≔ (γ₁ ⟨ x ⟩)) +ᶜ ((p ·ᶜ δ) , x ≔ _)
         ≡⟨ update-linear-+ᶜ γ (p ·ᶜ δ) _ _ x ⟩
       ((γ +ᶜ p ·ᶜ δ) , x ≔ _)
         ≡⟨ cong₃ _,_≔_ refl refl (cong₂ (Modality._+_ 𝕄) refl
                  (PE.sym (lookup-linear-·ᶜ δ₁ p x))) ⟩
       ((γ +ᶜ p ·ᶜ δ) , x ≔ _)
         ≡⟨ cong₃ _,_≔_ refl refl (PE.sym (lookup-linear-+ᶜ γ₁ (p ·ᶜ δ₁) x)) ⟩
       _ ∎

Conₘ-interchange (prodₘ {γ} {δ = δ} γ▸t γ▸t₁ refl) (prodₘ {γ₁} {δ = δ₁} δ▸t δ▸t₁ refl) x = prodₘ
  (Conₘ-interchange γ▸t δ▸t x)
  (Conₘ-interchange γ▸t₁ δ▸t₁ x)
  (subst₂ _≡_ (cong₃ _,_≔_ refl refl
                     (PE.sym (lookup-linear-+ᶜ γ₁ δ₁ x)))
              (PE.sym (update-linear-+ᶜ γ δ _ _ x)) refl)

Conₘ-interchange (fstₘ γ▸t) (fstₘ δ▸t) x = subst₂ _▸_ (PE.sym (update-self 𝟘ᶜ x)) refl (fstₘ γ▸t)
Conₘ-interchange (sndₘ γ▸t) (sndₘ δ▸t) x = subst₂ _▸_ (PE.sym (update-self 𝟘ᶜ x)) refl (sndₘ γ▸t)

Conₘ-interchange {𝕄 = 𝕄} (prodrecₘ {γ} {δ = δ} {p} γ▸t γ▸t₁) (prodrecₘ {γ₁} {δ = δ₁} δ▸t δ▸t₁) x =
  subst₂ _▸_ eq refl (prodrecₘ (Conₘ-interchange γ▸t δ▸t x) (Conₘ-interchange γ▸t₁ δ▸t₁ (x +1 +1)))
  where
  eq = begin
       p ·ᶜ (γ , x ≔ (γ₁ ⟨ x ⟩)) +ᶜ (δ , x ≔ (δ₁ ⟨ x ⟩))
         ≡⟨ cong₂ _+ᶜ_ (update-linear-·ᶜ γ p _ x) refl ⟩
       ((p ·ᶜ γ) , x ≔ _) +ᶜ (δ , x ≔ (δ₁ ⟨ x ⟩))
         ≡⟨ update-linear-+ᶜ (p ·ᶜ γ) δ _ _ x ⟩
       ((p ·ᶜ γ +ᶜ δ) , x ≔ _)
         ≡⟨ cong₃ _,_≔_ refl refl (cong₂ (Modality._+_ 𝕄)
                  (PE.sym (lookup-linear-·ᶜ γ₁ p x)) refl) ⟩
       ((p ·ᶜ γ +ᶜ δ) , x ≔ _)
         ≡⟨ cong₃ _,_≔_ refl refl
                  (PE.sym (lookup-linear-+ᶜ (p ·ᶜ γ₁) δ₁ x)) ⟩
       _ ∎

Conₘ-interchange zeroₘ zeroₘ x           = subst₂ _▸_ (PE.sym (update-self 𝟘ᶜ x)) refl zeroₘ
Conₘ-interchange (sucₘ γ▸t) (sucₘ δ▸t) x = sucₘ (Conₘ-interchange γ▸t δ▸t x)

Conₘ-interchange {𝕄 = 𝕄} (natrecₘ {γ} {r} {p} {δ} γ▸t γ▸t₁ γ▸t₂)
                     (natrecₘ {γ₁} {δ = δ₁} δ▸t δ▸t₁ δ▸t₂) x =
  subst₂ _▸_ eq refl
                (natrecₘ (Conₘ-interchange γ▸t δ▸t x) (Conₘ-interchange γ▸t₁ δ▸t₁ (x +1 +1))
                (Conₘ-interchange γ▸t₂ δ▸t₂ x))
  where
  r* = Modality._* 𝕄 r
  eq = begin
       r* ·ᶜ  ((γ , x ≔ (γ₁ ⟨ x ⟩)) +ᶜ p ·ᶜ (δ , x ≔ (δ₁ ⟨ x ⟩)))
         ≡⟨ cong (r* ·ᶜ_) (cong₂ _+ᶜ_ refl (update-linear-·ᶜ δ p (δ₁ ⟨ x ⟩) x)) ⟩
       r* ·ᶜ ((γ , x ≔ (γ₁ ⟨ x ⟩)) +ᶜ (p ·ᶜ δ , x ≔ _))
         ≡⟨ cong (r* ·ᶜ_) (update-linear-+ᶜ γ (p ·ᶜ δ) _ _ x) ⟩
       r* ·ᶜ ((γ +ᶜ p ·ᶜ δ) , x ≔ _)
         ≡⟨ cong (r* ·ᶜ_) (cong₃ _,_≔_ refl refl (cong₂ (Modality._+_ 𝕄) refl (PE.sym (lookup-linear-·ᶜ δ₁ p x)))) ⟩
       r* ·ᶜ ((γ +ᶜ p ·ᶜ δ) , x ≔ _)
         ≡⟨ cong (r* ·ᶜ_) (cong₃ _,_≔_ refl refl (PE.sym (lookup-linear-+ᶜ γ₁ (p ·ᶜ δ₁) x))) ⟩
       r* ·ᶜ ((γ +ᶜ p ·ᶜ δ) , x ≔ _) ≡⟨ update-linear-·ᶜ (γ +ᶜ p ·ᶜ δ) r* _ x ⟩
       ((r* ·ᶜ (γ +ᶜ p ·ᶜ δ)) , x ≔ _)
         ≡⟨ cong₃ _,_≔_ refl refl (PE.sym (lookup-linear-·ᶜ (γ₁ +ᶜ p ·ᶜ δ₁) r* x)) ⟩
       _ ∎

Conₘ-interchange (Emptyrecₘ γ▸t) (Emptyrecₘ δ▸t) x = Emptyrecₘ (Conₘ-interchange γ▸t δ▸t x)
Conₘ-interchange starₘ starₘ x = subst₂ _▸_ (PE.sym (update-self 𝟘ᶜ x)) refl starₘ

-- ⌈ t ⌉ is an upper bound on valid modality contexts

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
usage-upper-bound (natrecₘ {γ = γ} {r = r} {p = p} {s = s} x x₁ x₂) = ·ᶜ-monotone (+ᶜ-monotone₂
  (subst₂ _≤ᶜ_ (∧ᶜ-Idempotent γ) refl (∧ᶜ-monotone₂ (usage-upper-bound x) eq))
  (·ᶜ-monotone (usage-upper-bound x₂)))
  where
  eq = begin
         tailₘ (tailₘ (γ ∙ r ∙ p))
           ≡⟨ cong tailₘ (cong tailₘ (usage-upper-bound x₁)) ⟩
         tailₘ (tailₘ (γ ∙ r ∙ p ∧ᶜ ⌈ s ⌉))
           ≡⟨ cong tailₘ (tail-linear∧ {γ = γ ∙ r ∙ p} {⌈ s ⌉}) ⟩
         tailₘ ((γ ∙ r) ∧ᶜ tailₘ ⌈ s ⌉)
           ≡⟨ tail-linear∧ {γ = γ ∙ r} {tailₘ ⌈ s ⌉} ⟩
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
