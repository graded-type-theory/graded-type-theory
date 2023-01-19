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

Conₘ-interchange (prodᵣₘ {γ} {δ = δ} γ▸t γ▸t₁ PE.refl)
                 (prodᵣₘ {γ₁} {δ = δ₁} δ▸t δ▸t₁ PE.refl) x =
  prodᵣₘ (Conₘ-interchange γ▸t δ▸t x)
         (Conₘ-interchange γ▸t₁ δ▸t₁ x)
         (subst₂ _≡_ (cong (_ , _ ≔_) (PE.sym (lookup-distrib-+ᶜ γ₁ δ₁ x)))
                 (update-distrib-+ᶜ γ δ _ _ x) PE.refl)

Conₘ-interchange (prodₚₘ γ▸t γ▸u) (prodₚₘ δ▸t δ▸u) x =
  prodₚₘ (Conₘ-interchange γ▸t δ▸t x) (Conₘ-interchange γ▸u δ▸u x)

Conₘ-interchange (fstₘ γ▸t) (fstₘ δ▸t) x =
  fstₘ (Conₘ-interchange γ▸t δ▸t x)
Conₘ-interchange (sndₘ γ▸t) (sndₘ δ▸t) x =
  sndₘ (Conₘ-interchange γ▸t δ▸t x)

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

usage-upper-bound (prodᵣₘ t u PE.refl) =
  +ᶜ-monotone (usage-upper-bound t) (usage-upper-bound u)
usage-upper-bound (prodₚₘ t u) =
  ≤ᶜ-trans (≤ᶜ-reflexive (≈ᶜ-sym (∧ᶜ-idem _)))
           (∧ᶜ-monotone (usage-upper-bound t) (usage-upper-bound u))
usage-upper-bound (fstₘ t) = usage-upper-bound t
usage-upper-bound (sndₘ t) = usage-upper-bound t
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

usage-inf : γ ▸ t → ⌈ t ⌉ ▸ t
usage-inf Uₘ = Uₘ
usage-inf ℕₘ = ℕₘ
usage-inf Emptyₘ = Emptyₘ
usage-inf Unitₘ = Unitₘ
usage-inf (Πₘ {q = q} {G = G} γ▸F δ▸G) =
  Πₘ (usage-inf γ▸F)
     (sub (usage-inf δ▸G)
          (subst (tailₘ ⌈ G ⌉ ∙ q ≤ᶜ_) (headₘ-tailₘ-correct ⌈ G ⌉)
                 (≤ᶜ-refl ∙ headₘ-monotone (usage-upper-bound δ▸G))))
usage-inf (Σₘ {q = q} {G = G} γ▸F δ▸G) =
  Σₘ (usage-inf γ▸F)
     (sub (usage-inf δ▸G)
          (subst (tailₘ ⌈ G ⌉ ∙ q ≤ᶜ_) (headₘ-tailₘ-correct ⌈ G ⌉)
                 (≤ᶜ-refl ∙ headₘ-monotone (usage-upper-bound δ▸G))))
usage-inf var = var
usage-inf (lamₘ {p = p} {t = t} γ▸t) =
  lamₘ (sub (usage-inf γ▸t)
            (PE.subst (⌈ lam p t ⌉ ∙ p ≤ᶜ_)
                      (headₘ-tailₘ-correct ⌈ t ⌉)
                      (≤ᶜ-refl ∙ headₘ-monotone (usage-upper-bound γ▸t))))
usage-inf (γ▸t ∘ₘ γ▸t₁) = usage-inf γ▸t ∘ₘ usage-inf γ▸t₁
usage-inf (prodᵣₘ γ▸t γ▸t₁ PE.refl) = prodᵣₘ (usage-inf γ▸t) (usage-inf γ▸t₁) PE.refl
usage-inf (prodₚₘ γ▸t γ▸t₁) = prodₚₘ (sub (usage-inf γ▸t) (∧ᶜ-decreasingˡ _ _))
                                     (sub (usage-inf γ▸t₁) (∧ᶜ-decreasingʳ _ _))
usage-inf (fstₘ γ▸t) = fstₘ (usage-inf γ▸t)
usage-inf (sndₘ γ▸t) = sndₘ (usage-inf γ▸t)
usage-inf (prodrecₘ {p = p} {u = u} γ▸t δ▸u) =
  prodrecₘ (usage-inf γ▸t)
           (sub (usage-inf δ▸u)
                (subst (tailₘ (tailₘ ⌈ u ⌉) ∙ p ∙ p ≤ᶜ_)
                       (PE.trans (cong (_∙ headₘ ⌈ u ⌉) (headₘ-tailₘ-correct (tailₘ ⌈ u ⌉))) (headₘ-tailₘ-correct ⌈ u ⌉))
                       (≤ᶜ-refl ∙ headₘ-monotone (tailₘ-monotone (usage-upper-bound δ▸u)) ∙ headₘ-monotone (usage-upper-bound δ▸u))))
usage-inf zeroₘ = zeroₘ
usage-inf (sucₘ γ▸t) = sucₘ (usage-inf γ▸t)
usage-inf (natrecₘ {p = p} {r = r} {s = s} γ▸z δ▸s η▸n) =
  natrecₘ (usage-inf γ▸z)
          (sub (usage-inf δ▸s)
               (subst (tailₘ (tailₘ ⌈ s ⌉) ∙ p ∙ r ≤ᶜ_)
                      (PE.trans (cong (_∙ headₘ ⌈ s ⌉) (headₘ-tailₘ-correct (tailₘ ⌈ s ⌉))) (headₘ-tailₘ-correct ⌈ s ⌉))
                      (≤ᶜ-refl ∙ headₘ-monotone (tailₘ-monotone (usage-upper-bound δ▸s)) ∙ headₘ-monotone (usage-upper-bound δ▸s))))
          (usage-inf η▸n)
usage-inf (Emptyrecₘ γ▸t) = Emptyrecₘ (usage-inf γ▸t)
usage-inf starₘ = starₘ
usage-inf (sub γ▸t x) = usage-inf γ▸t

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
