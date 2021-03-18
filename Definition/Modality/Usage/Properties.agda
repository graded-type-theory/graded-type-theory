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


record InvUsageNatrec {m} {M} {𝕄 : Modality M} (γ : Conₘ 𝕄 m) (p q : M)
                      (z : Term M m) (s : Term M (1+ (1+ m))) (n : Term M m) : Set where
  constructor invUsageNatrec
  field
    {δ η} : Conₘ 𝕄 m
    δ▸z   : δ ▸ z
    δ▸s   : δ ∙ q ∙ p ▸ s
    η▸n   : η ▸ n
    γ≤γ′  : γ ≤ᶜ (Modality._* 𝕄 q) ·ᶜ (δ +ᶜ p ·ᶜ η)

-- If γ ▸ natrec p q G z s n then δ ▸ z, δ ∙ q ∙ p ▸ s, η ▸ n and γ ≤ᶜ q* ·ᶜ (δ +ᶜ p ·ᶜ η)

inv-usage-natrec : {m : Nat} {𝕄 : Modality M} {γ : Conₘ 𝕄 m} {p q : M} {z n : Term M m}
                   {G : Term M (1+ m)} {s : Term M (1+ (1+ m))}
                 → γ ▸ natrec p q G z s n → InvUsageNatrec γ p q z s n
inv-usage-natrec (natrecₘ δ▸z δ▸s η▸n) = invUsageNatrec δ▸z δ▸s η▸n ≤ᶜ-reflexive
inv-usage-natrec (sub γ▸natrec γ≤γ′) with inv-usage-natrec γ▸natrec
... | invUsageNatrec δ▸z δ▸s η▸n γ′≤γ″ = invUsageNatrec δ▸z δ▸s η▸n (≤ᶜ-transitive γ≤γ′ γ′≤γ″)


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
