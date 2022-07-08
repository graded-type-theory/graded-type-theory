{-# OPTIONS --without-K --safe #-}

open import Tools.Relation
open import Definition.Modality

module Definition.Modality.Usage.Properties {a ℓ}
  {M′ : Setoid a ℓ} (𝕄 : Modality M′)
  where

open Modality 𝕄
open Setoid M′ renaming (Carrier to M)

open import Definition.Modality.Context 𝕄
open import Definition.Modality.Context.Properties 𝕄
open import Definition.Modality.Properties 𝕄
open import Definition.Modality.Usage 𝕄
open import Definition.Modality.Usage.Inversion 𝕄
open import Definition.Typed M′ hiding (_∙_)
open import Definition.Untyped M hiding (_∷_ ; _∙_ ; ε ; subst)
open import Definition.Usage 𝕄

open import Tools.Fin
open import Tools.Nat hiding (_+_)
open import Tools.Product
open import Tools.PropositionalEquality as PE


private
  variable
    n : Nat
    Γ : Con Term n
    t u A F : Term n
    G : Term (1+ n)
    γ δ η : Conₘ n
    p q r : M

-- The contents of two valid modality contexts can be freely interchanged
-- If γ ▸ t and δ ▸ t then, for any x, (γ , x ≔ δ⟨x⟩) ▸ t

Conₘ-interchange : γ ▸ t → δ ▸ t → (x : Fin n) →
            let p = δ ⟨ x ⟩
            in  (γ , x ≔ p) ▸ t
Conₘ-interchange (sub γ▸t γ≤γ′) δ▸t x  = sub
  (Conₘ-interchange γ▸t δ▸t x)
  (update-monotoneˡ x γ≤γ′)
Conₘ-interchange γ▸t (sub γ′▸t δ≤γ′) x = sub
  (Conₘ-interchange γ▸t γ′▸t x)
  (update-monotoneʳ x (lookup-monotone x δ≤γ′))
Conₘ-interchange Uₘ Uₘ x =
  subst (_▸ _) (PE.sym (update-self 𝟘ᶜ x)) Uₘ
Conₘ-interchange ℕₘ ℕₘ x =
  subst (_▸ _) (PE.sym (update-self 𝟘ᶜ x)) ℕₘ
Conₘ-interchange Emptyₘ Emptyₘ x =
  subst (_▸ _) (PE.sym (update-self 𝟘ᶜ x)) Emptyₘ
Conₘ-interchange Unitₘ Unitₘ x =
  subst (_▸ _) (PE.sym (update-self 𝟘ᶜ x)) Unitₘ

Conₘ-interchange (Πₘ {γ} {δ = δ} γ▸t δ▸u)
                 (Πₘ {γ′} {δ = δ′} γ′▸t δ′▸u) x =
  subst (_▸ _) eq (Πₘ (Conₘ-interchange γ▸t γ′▸t x)
                      (Conₘ-interchange δ▸u δ′▸u (x +1)))
  where
  open import Tools.Reasoning.PropositionalEquality
  eq = begin
    (γ , x ≔ γ′ ⟨ x ⟩) +ᶜ (δ , x ≔ δ′ ⟨ x ⟩)
      ≡˘⟨ update-distrib-+ᶜ γ δ _ _ x ⟩
    (γ +ᶜ δ , x ≔ γ′ ⟨ x ⟩ + δ′ ⟨ x ⟩)
      ≡˘⟨ cong ((γ +ᶜ δ) , x ≔_) (lookup-distrib-+ᶜ γ′ δ′ x) ⟩
    (γ +ᶜ δ) , x ≔ ((γ′ +ᶜ δ′) ⟨ x ⟩)        ∎

Conₘ-interchange (Σₘ {γ} {δ = δ} γ▸t δ▸u)
                 (Σₘ {γ′} {δ = δ′} γ′▸t δ′▸u) x =
  subst (_▸ _) eq (Σₘ (Conₘ-interchange γ▸t γ′▸t x)
                      (Conₘ-interchange δ▸u δ′▸u (x +1)))
  where
  open import Tools.Reasoning.PropositionalEquality
  eq = begin
    (γ , x ≔ γ′ ⟨ x ⟩) +ᶜ (δ , x ≔ δ′ ⟨ x ⟩)
      ≡˘⟨ update-distrib-+ᶜ γ δ _ _ x ⟩
    (γ +ᶜ δ , x ≔ γ′ ⟨ x ⟩ + δ′ ⟨ x ⟩)
      ≡˘⟨ cong ((γ +ᶜ δ) , x ≔_) (lookup-distrib-+ᶜ γ′ δ′ x) ⟩
    (γ +ᶜ δ) , x ≔ ((γ′ +ᶜ δ′) ⟨ x ⟩)        ∎

Conₘ-interchange (var {x₁}) var x = subst (_▸ _)
  (PE.sym (update-self (𝟘ᶜ , x₁ ≔ (Modality.𝟙 𝕄)) x)) var

Conₘ-interchange (lamₘ γ▸t) (lamₘ δ▸t) x = lamₘ (Conₘ-interchange γ▸t δ▸t (x +1))

Conₘ-interchange (_∘ₘ_ {γ} {δ = δ} {p = p} γ▸t δ▸u)
                 (_∘ₘ_ {γ′} {δ = δ′} γ′▸t δ′▸u) x =
  subst (_▸ _) eq ((Conₘ-interchange γ▸t γ′▸t x) ∘ₘ (Conₘ-interchange δ▸u δ′▸u x))
  where
  open import Tools.Reasoning.PropositionalEquality
  eq = begin
    (γ , x ≔ (γ′ ⟨ x ⟩)) +ᶜ p ·ᶜ (δ , x ≔ (δ′ ⟨ x ⟩))
       ≡˘⟨ cong (_ +ᶜ_) (update-distrib-·ᶜ δ p _ x) ⟩
    (γ , x ≔ (γ′ ⟨ x ⟩)) +ᶜ (p ·ᶜ δ , x ≔ (p · δ′ ⟨ x ⟩))
       ≡˘⟨ cong (_ +ᶜ_) (cong (_ , x ≔_) (lookup-distrib-·ᶜ δ′ p x)) ⟩
    (γ , x ≔ (γ′ ⟨ x ⟩)) +ᶜ (p ·ᶜ δ , x ≔ ((p ·ᶜ δ′) ⟨ x ⟩))
       ≡˘⟨ update-distrib-+ᶜ γ _ _ _ x ⟩
    (γ +ᶜ p ·ᶜ δ) , x ≔ γ′ ⟨ x ⟩ + (p ·ᶜ δ′) ⟨ x ⟩
       ≡˘⟨ cong (_ , x ≔_) (lookup-distrib-+ᶜ γ′ (p ·ᶜ δ′) x) ⟩
    (γ +ᶜ p ·ᶜ δ) , x ≔ (γ′ +ᶜ p ·ᶜ δ′) ⟨ x ⟩ ∎

Conₘ-interchange (prodₘ {γ} {δ = δ} γ▸t γ▸t₁ PE.refl)
                 (prodₘ {γ₁} {δ = δ₁} δ▸t δ▸t₁ PE.refl) x =
  prodₘ
    (Conₘ-interchange γ▸t δ▸t x)
    (Conₘ-interchange γ▸t₁ δ▸t₁ x)
    (subst₂ _≡_ (cong (_ , _ ≔_) (PE.sym (lookup-distrib-+ᶜ γ₁ δ₁ x)))
                (update-distrib-+ᶜ γ δ _ _ x) PE.refl)

Conₘ-interchange (fstₘ γ▸t) (fstₘ δ▸t) x =
  subst (_▸ _) (PE.sym (update-self 𝟘ᶜ x)) (fstₘ γ▸t)
Conₘ-interchange (sndₘ γ▸t) (sndₘ δ▸t) x =
  subst (_▸ _) (PE.sym (update-self 𝟘ᶜ x)) (sndₘ γ▸t)

Conₘ-interchange (prodrecₘ {γ = γ} {δ = δ} {p} γ▸t δ▸t)
                 (prodrecₘ {γ = γ′} {δ = δ′} γ▸t₁ δ▸t₁) x =
  subst (_▸ _) eq (prodrecₘ (Conₘ-interchange γ▸t γ▸t₁ x)
                              (Conₘ-interchange δ▸t δ▸t₁ (x +1 +1)))
  where
  open import Tools.Reasoning.PropositionalEquality
  eq = begin
    p ·ᶜ (γ , x ≔ γ′ ⟨ x ⟩) +ᶜ (δ , x ≔ δ′ ⟨ x ⟩)
      ≡˘⟨ cong (_+ᶜ _) (update-distrib-·ᶜ γ p (γ′ ⟨ x ⟩) x) ⟩
    (p ·ᶜ γ , x ≔ p · γ′ ⟨ x ⟩) +ᶜ (δ , x ≔ δ′ ⟨ x ⟩)
      ≡˘⟨ update-distrib-+ᶜ (p ·ᶜ γ) δ (p · γ′ ⟨ x ⟩) (δ′ ⟨ x ⟩) x ⟩
    p ·ᶜ γ +ᶜ δ , x ≔ p · γ′ ⟨ x ⟩ + δ′ ⟨ x ⟩
      ≡˘⟨ cong (λ y → _ , x ≔ y + _) (lookup-distrib-·ᶜ γ′ p x) ⟩
    p ·ᶜ γ +ᶜ δ , x ≔ (p ·ᶜ γ′) ⟨ x ⟩ + δ′ ⟨ x ⟩
      ≡˘⟨ cong (λ y → _ , x ≔ y) (lookup-distrib-+ᶜ (p ·ᶜ γ′) δ′ x) ⟩
    p ·ᶜ γ +ᶜ δ , x ≔ (p ·ᶜ γ′ +ᶜ δ′) ⟨ x ⟩ ∎

Conₘ-interchange zeroₘ zeroₘ x           =
  subst (_▸ _) (PE.sym (update-self 𝟘ᶜ x)) zeroₘ
Conₘ-interchange (sucₘ γ▸t) (sucₘ δ▸t) x =
  sucₘ (Conₘ-interchange γ▸t δ▸t x)

Conₘ-interchange (natrecₘ {γ = γ} {δ = δ} {p = p} {r = r} {η = η} γ▸z δ▸s η▸n)
                 (natrecₘ {γ = γ′} {δ = δ′} {η = η′} γ′▸z δ′▸s η′▸n) x =
  subst (_▸ _) eq (natrecₘ (Conₘ-interchange γ▸z γ′▸z x)
                           (Conₘ-interchange δ▸s δ′▸s (x +1 +1))
                           (Conₘ-interchange η▸n η′▸n x))
  where
  open import Tools.Reasoning.PropositionalEquality
  eq = let γ'  = γ , x ≔ (γ′ ⟨ x ⟩)
           δ'  = δ , x ≔ (δ′ ⟨ x ⟩)
           η'  = η , x ≔ (η′ ⟨ x ⟩)
           pη' = p ·ᶜ η , x ≔ (p · (η′ ⟨ x ⟩))
       in begin
          (γ' ∧ᶜ η') ⊛ᶜ (δ' +ᶜ p ·ᶜ η') ▷ r
            ≡˘⟨ cong (λ y → _ ⊛ᶜ (_ +ᶜ y) ▷ r)
                     (update-distrib-·ᶜ η p (η′ ⟨ x ⟩) x) ⟩
          (γ' ∧ᶜ η') ⊛ᶜ (δ' +ᶜ pη') ▷ r
            ≡˘⟨ cong (λ y → _ ⊛ᶜ (_ +ᶜ (_ , x ≔ y)) ▷ r)
                     (lookup-distrib-·ᶜ η′ p x) ⟩
          (γ' ∧ᶜ η') ⊛ᶜ (δ' +ᶜ ((p ·ᶜ η) , x ≔ ((p ·ᶜ η′) ⟨ x ⟩))) ▷ r
            ≡˘⟨ cong (λ y →  _ ⊛ᶜ y ▷ r)
                     (update-distrib-+ᶜ δ (p ·ᶜ η) (δ′ ⟨ x ⟩) ((p ·ᶜ η′) ⟨ x ⟩) x) ⟩
          (γ' ∧ᶜ η') ⊛ᶜ ((δ +ᶜ p ·ᶜ η) , x ≔ (δ′ ⟨ x ⟩ + (p ·ᶜ η′) ⟨ x ⟩)) ▷ r
            ≡˘⟨ cong₂ (λ y z → y ⊛ᶜ (_ , x ≔ z) ▷ r)
                      (update-distrib-∧ᶜ γ η (γ′ ⟨ x ⟩) (η′ ⟨ x ⟩) x)
                      (lookup-distrib-+ᶜ δ′ (p ·ᶜ η′) x)   ⟩
          ((γ ∧ᶜ η) , x ≔ (γ′ ⟨ x ⟩ ∧ η′ ⟨ x ⟩)) ⊛ᶜ ((δ +ᶜ p ·ᶜ η) , x ≔ ((δ′ +ᶜ p ·ᶜ η′) ⟨ x ⟩)) ▷ r
            ≡˘⟨ update-distrib-⊛ᶜ (γ ∧ᶜ η) (δ +ᶜ p ·ᶜ η) r
                                   ((γ′ ⟨ x ⟩) ∧ (η′ ⟨ x ⟩))
                                   ((δ′ +ᶜ p ·ᶜ η′) ⟨ x ⟩) x ⟩
          (γ ∧ᶜ η) ⊛ᶜ (δ +ᶜ p ·ᶜ η) ▷ r , x ≔ ((γ′ ⟨ x ⟩) ∧ (η′ ⟨ x ⟩)) ⊛ ((δ′ +ᶜ p ·ᶜ η′) ⟨ x ⟩) ▷ r
            ≡˘⟨ cong (λ y → _ , x ≔ y ⊛ _ ▷ _) (lookup-distrib-∧ᶜ γ′ η′ x) ⟩
          (γ ∧ᶜ η) ⊛ᶜ (δ +ᶜ p ·ᶜ η) ▷ r , x ≔ ((γ′ ∧ᶜ η′) ⟨ x ⟩) ⊛ ((δ′ +ᶜ p ·ᶜ η′) ⟨ x ⟩) ▷ r
            ≡˘⟨ cong (λ y → _ , x ≔ y) (lookup-distrib-⊛ᶜ (γ′ ∧ᶜ η′) (δ′ +ᶜ p ·ᶜ η′) r x) ⟩
          (γ ∧ᶜ η) ⊛ᶜ (δ +ᶜ (p ·ᶜ η)) ▷ r , x ≔ ((γ′ ∧ᶜ η′) ⊛ᶜ (δ′ +ᶜ (p ·ᶜ η′)) ▷ r) ⟨ x ⟩ ∎

Conₘ-interchange (Emptyrecₘ {γ} {p = p} γ▸t) (Emptyrecₘ {δ} δ▸t) x =
  subst (_▸ _) eq (Emptyrecₘ (Conₘ-interchange γ▸t δ▸t x))
  where
  open import Tools.Reasoning.PropositionalEquality
  eq = begin
    p ·ᶜ (γ , x ≔ δ ⟨ x ⟩)      ≡˘⟨ update-distrib-·ᶜ γ p (δ ⟨ x ⟩) x ⟩
    p ·ᶜ γ , x ≔ p · (δ ⟨ x ⟩)  ≡˘⟨ cong (_ , _ ≔_) (lookup-distrib-·ᶜ δ p x) ⟩
    p ·ᶜ γ , x ≔ (p ·ᶜ δ) ⟨ x ⟩ ∎

Conₘ-interchange starₘ starₘ x =
  subst (_▸ _) (PE.sym (update-self 𝟘ᶜ x)) starₘ


-- ⌈ t ⌉ is an upper bound on valid modality contexts
-- If γ ▸ t, then γ ≤ ⌈ t ⌉

usage-upper-bound : γ ▸ t → γ ≤ᶜ ⌈ t ⌉
usage-upper-bound Uₘ     = ≤ᶜ-refl
usage-upper-bound ℕₘ     = ≤ᶜ-refl
usage-upper-bound Emptyₘ = ≤ᶜ-refl
usage-upper-bound Unitₘ  = ≤ᶜ-refl

usage-upper-bound (Πₘ {δ = δ} {q} {G₁} F G) =
  +ᶜ-monotone (usage-upper-bound F)
              (subst (δ ≈ᶜ_) (tailₘ-distrib-∧ᶜ (δ ∙ q) ⌈ G₁ ⌉)
                     (tailₘ-cong (usage-upper-bound G)))

usage-upper-bound (Σₘ {δ = δ} {q} {G₁} F G) =
  +ᶜ-monotone (usage-upper-bound F)
              (subst (δ ≈ᶜ_) (tailₘ-distrib-∧ᶜ (δ ∙ q) ⌈ G₁ ⌉)
                     (tailₘ-cong (usage-upper-bound G)))

usage-upper-bound var = ≤ᶜ-refl

usage-upper-bound {γ = γ} (lamₘ {p = p} {t₁} t) =
  subst (γ ≈ᶜ_) (tailₘ-distrib-∧ᶜ (γ ∙ p) ⌈ t₁ ⌉)
        (tailₘ-cong (usage-upper-bound t))

usage-upper-bound (t ∘ₘ u) =
  +ᶜ-monotone (usage-upper-bound t)
              (·ᶜ-monotoneʳ (usage-upper-bound u))

usage-upper-bound (prodₘ! t u)   =
  +ᶜ-monotone (usage-upper-bound t) (usage-upper-bound u)
usage-upper-bound (fstₘ t) = ≤ᶜ-refl
usage-upper-bound (sndₘ t) = ≤ᶜ-refl
usage-upper-bound (prodrecₘ t u) =
  +ᶜ-monotone (·ᶜ-monotoneʳ (usage-upper-bound t))
              (tailₘ-monotone (tailₘ-monotone (usage-upper-bound u)))

usage-upper-bound zeroₘ    = ≤ᶜ-refl
usage-upper-bound (sucₘ t) = usage-upper-bound t

usage-upper-bound (natrecₘ {z = z} {s = s} {n = n} γ▸z δ▸s η▸n) =
  ⊛ᶜ-monotone (∧ᶜ-monotone γ≤γ′ η≤η′)
               (+ᶜ-monotone (tailₘ-monotone (tailₘ-monotone δ≤δ′))
                            (·ᶜ-monotoneʳ η≤η′))
  where
  γ≤γ′ = usage-upper-bound γ▸z
  δ≤δ′ = usage-upper-bound δ▸s
  η≤η′ = usage-upper-bound η▸n

usage-upper-bound (Emptyrecₘ e) =
  ·ᶜ-monotoneʳ (usage-upper-bound e)
usage-upper-bound starₘ = ≤ᶜ-refl
usage-upper-bound (sub t x) = ≤ᶜ-trans x (usage-upper-bound t)


-- A valid modality context can be computed from well typed and well resourced terms
-- If Γ ⊢ t ∷ A and γ ▸ t, then ⌈ t ⌉ ▸ t

usage-calc-term′ : {Γ : Con Term n} {γ : Conₘ n} {t A : Term n}
                 → Γ ⊢ t ∷ A → γ ▸ t → ⌈ t ⌉ ▸ t
usage-calc-term′ (Πⱼ_▹_ {q = q} {G = G} Γ⊢F:U Γ⊢G:U) γ▸t with inv-usage-Π γ▸t
... | invUsageΠΣ δ▸F η▸G _ =
  Πₘ (usage-calc-term′ Γ⊢F:U δ▸F)
     (subst₂ _▸_ (update-head ⌈ G ⌉ q) PE.refl
                 (Conₘ-interchange (usage-calc-term′ Γ⊢G:U η▸G) η▸G x0))
usage-calc-term′  (Σⱼ_▹_ {q = q} {G = G} Γ⊢F:U Γ⊢G:U) γ▸t with inv-usage-Σ γ▸t
... | invUsageΠΣ δ▸F η▸G _ =
  Σₘ (usage-calc-term′ Γ⊢F:U δ▸F)
     (subst₂ _▸_ (update-head ⌈ G ⌉ q) PE.refl
                 (Conₘ-interchange (usage-calc-term′ Γ⊢G:U η▸G) η▸G x0))
usage-calc-term′ (ℕⱼ x) γ▸t = ℕₘ
usage-calc-term′ (Emptyⱼ x) γ▸t = Emptyₘ
usage-calc-term′ (Unitⱼ x) γ▸t = Unitₘ
usage-calc-term′ (var x x₁) γ▸t = var
usage-calc-term′ (lamⱼ {p = p} {t = t} x Γ⊢t:A) γ▸λt with inv-usage-lam γ▸λt
... | invUsageLam δ▸t _ = lamₘ (subst₂ _▸_ (update-head ⌈ t ⌉ p) PE.refl
                               (Conₘ-interchange (usage-calc-term′ Γ⊢t:A δ▸t) δ▸t x0))
usage-calc-term′ (Γ⊢t:Π ∘ⱼ Γ⊢u:F) γ▸t with inv-usage-app γ▸t
... | invUsageApp δ▸t η▸u _ =
    (usage-calc-term′ Γ⊢t:Π δ▸t) ∘ₘ (usage-calc-term′ Γ⊢u:F η▸u)
usage-calc-term′ (prodⱼ x x₁ Γ⊢t:A Γ⊢u:B) γ▸t with inv-usage-prod γ▸t
... | invUsageProd δ▸t η▸u _ _ =
  prodₘ (usage-calc-term′ Γ⊢t:A δ▸t)
        (usage-calc-term′ Γ⊢u:B η▸u)
        PE.refl
usage-calc-term′ (fstⱼ x x₁ Γ⊢t:A) γ▸t with inv-usage-fst γ▸t
... | invUsageProj 𝟘▸t _ = fstₘ 𝟘▸t
usage-calc-term′ (sndⱼ x x₁ Γ⊢t:A) γ▸t with inv-usage-snd γ▸t
... | invUsageProj 𝟘▸t _ = sndₘ 𝟘▸t
usage-calc-term′ (prodrecⱼ {p = p} {u = u} x x₁ x₂ Γ⊢t:A Γ⊢u:B) γ▸t with inv-usage-prodrec γ▸t
... | invUsageProdrec {δ = δ} {η} δ▸t η▸u γ≤γ′ =
  prodrecₘ (usage-calc-term′ Γ⊢t:A δ▸t)
           (subst (_▸ _) eq
                  (Conₘ-interchange (Conₘ-interchange (usage-calc-term′ Γ⊢u:B η▸u)
                                                      η▸u (x0 +1))
                                    η▸u x0))
  where
  open import Tools.Reasoning.PropositionalEquality
  eq = begin
    (⌈ u ⌉ , x0 +1 ≔ p) , x0 ≔ p
      ≡⟨ cong (λ γ → γ , x0 ≔ p) (update-step ⌈ u ⌉ p x0) ⟩
    tailₘ ⌈ u ⌉ , x0 ≔ p ∙ p
      ≡⟨ cong (_∙ p) (update-head (tailₘ ⌈ u ⌉) p) ⟩
    tailₘ (tailₘ ⌈ u ⌉) ∙ p ∙ p ∎

usage-calc-term′ (zeroⱼ x) γ▸t = zeroₘ
usage-calc-term′ (sucⱼ Γ⊢t:ℕ) γ▸t  with inv-usage-suc γ▸t
... | invUsageSuc δ▸t _ = sucₘ (usage-calc-term′ Γ⊢t:ℕ δ▸t)

usage-calc-term′ (natrecⱼ {p = p} {r = r} {s = s} {z = z} {n = n}
                 x Γ⊢z:G Γ⊢s:G Γ⊢n:ℕ) γ▸t with inv-usage-natrec γ▸t
... | invUsageNatrec {δ = δ} {η} {θ} δ▸z η▸s θ▸n a =
  natrecₘ (usage-calc-term′ Γ⊢z:G δ▸z)
          (subst (_▸ _) eq
                 (Conₘ-interchange (Conₘ-interchange (usage-calc-term′ Γ⊢s:G η▸s)
                                                     η▸s (x0 +1))
                                   η▸s x0))
  (usage-calc-term′ Γ⊢n:ℕ θ▸n)
  where
  open import Tools.Reasoning.PropositionalEquality
  ηs = ⌈ s ⌉
  eq =  begin
     (ηs , x0 +1 ≔ p) , x0 ≔ r
       ≡⟨ cong (_, x0 ≔ r) (update-step ηs p x0) ⟩
     ((tailₘ ηs , x0 ≔ p) ∙ headₘ ηs) , x0 ≔ r
       ≡⟨ cong (_, x0 ≔ r) (cong (_∙ p) (update-head (tailₘ ηs) p)) ⟩
     (tailₘ (tailₘ ηs) ∙ p ∙ headₘ ηs) , x0 ≔ r
       ≡⟨ update-head ((tailₘ (tailₘ ηs) ∙ p) ∙ headₘ ηs) r ⟩
     tailₘ (tailₘ ηs) ∙ p ∙ r ∎

usage-calc-term′ (Emptyrecⱼ x Γ⊢t:A) γ▸t with inv-usage-Emptyrec γ▸t
... | invUsageEmptyrec δ▸t _ = Emptyrecₘ (usage-calc-term′ Γ⊢t:A δ▸t)
usage-calc-term′ (starⱼ x) γ▸t = starₘ
usage-calc-term′ (conv Γ⊢t:A x) γ▸t = usage-calc-term′ Γ⊢t:A γ▸t

-- A valid modality context can be computed from well typed and well resourced terms
-- If Γ ⊢ γ ▸ t ∷ A ◂ δ, then ⌈ t ⌉ ▸ t

usage-calc-term : Γ ⊢ γ ▸ t ∷ A ◂ δ → ⌈ t ⌉ ▸ t
usage-calc-term (Γ⊢t:A , γ▸t , δ▸A) = usage-calc-term′ Γ⊢t:A γ▸t


-- A valid modality context can be computed from well typed and well resourced types
-- If Γ ⊢ A ◂ γ, then ⌈ A ⌉ ▸ A

usage-calc-type : Γ ⊢ A ◂ γ → ⌈ A ⌉ ▸ A
usage-calc-type (Uⱼ x , γ▸A) = Uₘ
usage-calc-type (ℕⱼ x , γ▸A) = ℕₘ
usage-calc-type (Emptyⱼ x , γ▸A) = Emptyₘ
usage-calc-type (Unitⱼ x , γ▸A) = Unitₘ
usage-calc-type (Πⱼ_▹_ {G = G} {q = q} Γ⊢F Γ⊢G , γ▸Π) with inv-usage-Π γ▸Π
... | invUsageΠΣ δ▸F η▸G _ =
  Πₘ (usage-calc-type (Γ⊢F , δ▸F))
     (subst (_▸ _) (update-head ⌈ G ⌉ q)
                   (Conₘ-interchange (usage-calc-type (Γ⊢G , η▸G)) η▸G x0))
usage-calc-type (Σⱼ_▹_ {G = G} {q = q} Γ⊢F Γ⊢G , γ▸Σ) with inv-usage-Σ γ▸Σ
... | invUsageΠΣ δ▸F η▸G _ =
  Σₘ (usage-calc-type (Γ⊢F , δ▸F))
     (subst (_▸ _) (update-head ⌈ G ⌉ q)
                   (Conₘ-interchange (usage-calc-type (Γ⊢G , η▸G)) η▸G x0))
usage-calc-type (univ Γ⊢A:U , γ▸A) = usage-calc-term′ Γ⊢A:U γ▸A


-- The context used in the usage rule for natrec satisfies the neccessary inequalities
-- (γ ∧ η) ⊛ᶜ (δ + pη) ▷ r ≤ γ and
-- (γ ∧ η) ⊛ᶜ (δ + pη) ▷ r ≤ δ + pη + r ((γ ∧ η) ⊛ᶜ (δ + pη) ▷ r) and
-- (γ ∧ η) ⊛ᶜ (δ + pη) ▷ r ≤ η

natrec-usage : (γ ∧ᶜ η) ⊛ᶜ (δ +ᶜ p ·ᶜ η) ▷ r ≤ᶜ γ
             × (γ ∧ᶜ η) ⊛ᶜ (δ +ᶜ p ·ᶜ η) ▷ r ≤ᶜ δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ (γ ∧ᶜ η) ⊛ᶜ (δ +ᶜ p ·ᶜ η) ▷ r
             × (γ ∧ᶜ η) ⊛ᶜ (δ +ᶜ p ·ᶜ η) ▷ r ≤ᶜ η
natrec-usage {γ = γ} {η} {δ} {p} {r} =
  ≤ᶜ-trans (⊛ᶜ-ineq₂ (γ ∧ᶜ η) (δ +ᶜ p ·ᶜ η) r) (∧ᶜ-decreasingˡ γ η)
  , ≤ᶜ-trans (⊛ᶜ-ineq₁ (γ ∧ᶜ η) (δ +ᶜ p ·ᶜ η) r)
             (≤ᶜ-reflexive (+ᶜ-assoc δ (p ·ᶜ η) (r ·ᶜ (γ ∧ᶜ η) ⊛ᶜ (δ +ᶜ p ·ᶜ η) ▷ r)))
  , ≤ᶜ-trans (⊛ᶜ-ineq₂ (γ ∧ᶜ η) (δ +ᶜ p ·ᶜ η) r) (∧ᶜ-decreasingʳ γ η)