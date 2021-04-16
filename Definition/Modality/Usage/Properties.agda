{-# OPTIONS --without-K --safe #-}

open import Tools.Relation
open import Definition.Modality

module Definition.Modality.Usage.Properties
  {M : Set} {_≈_ : Rel M _}
  (𝕄 : Modality M _≈_)
  where

open import Definition.Modality.Context 𝕄
open import Definition.Modality.Context.Properties 𝕄
open import Definition.Modality.Properties 𝕄
open import Definition.Modality.Usage 𝕄
open import Definition.Modality.Usage.Inversion 𝕄
open import Definition.Untyped M _≈_ as U hiding (_∷_ ; _∙_ ; ε)
open import Definition.Typed 𝕄 hiding (_∙_)

open import Tools.Fin
open import Tools.Nat hiding (_+_)
open import Tools.Product
open import Tools.PropositionalEquality as PE

open Modality 𝕄

private
  variable
    n : Nat
    Γ : Con Term n
    t u A F : Term n
    G : Term (1+ n)
    γ γ′ δ : Conₘ n
    p q : M

-- The contents of two valid modality context can be freely interchanged
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
Conₘ-interchange Uₘ Uₘ x         = subst₂ _▸_ (PE.sym (update-self 𝟘ᶜ x)) refl Uₘ
Conₘ-interchange ℕₘ ℕₘ x         = subst₂ _▸_ (PE.sym (update-self 𝟘ᶜ x)) refl ℕₘ
Conₘ-interchange Emptyₘ Emptyₘ x = subst₂ _▸_ (PE.sym (update-self 𝟘ᶜ x)) refl Emptyₘ
Conₘ-interchange Unitₘ Unitₘ x   = subst₂ _▸_ (PE.sym (update-self 𝟘ᶜ x)) refl Unitₘ

Conₘ-interchange (Πₘ {γ} {δ = δ} γ▸t δ▸u) (Πₘ {γ′} {δ = δ′} γ′▸t δ′▸u) x = subst₂ _▸_  eq refl
  (Πₘ (Conₘ-interchange γ▸t γ′▸t x) (Conₘ-interchange δ▸u δ′▸u (x +1)))
  where
  open import Tools.Reasoning.PropositionalEquality
  eq = begin
    (γ , x ≔ γ′ ⟨ x ⟩) +ᶜ (δ , x ≔ δ′ ⟨ x ⟩) ≡⟨ PE.sym (update-distrib-+ᶜ γ δ _ _ x) ⟩
    (γ +ᶜ δ , x ≔ γ′ ⟨ x ⟩ + δ′ ⟨ x ⟩)       ≡⟨ cong ((γ +ᶜ δ) , x ≔_) (PE.sym (lookup-distrib-+ᶜ γ′ δ′ x)) ⟩
    (γ +ᶜ δ) , x ≔ ((γ′ +ᶜ δ′) ⟨ x ⟩)        ∎

Conₘ-interchange (Σₘ {γ} {δ = δ} γ▸t δ▸u) (Σₘ {γ′} {δ = δ′} γ′▸t δ′▸u) x = subst₂ _▸_  eq refl
  (Σₘ (Conₘ-interchange γ▸t γ′▸t x) (Conₘ-interchange δ▸u δ′▸u (x +1)))
  where
  open import Tools.Reasoning.PropositionalEquality
  eq = begin
    (γ , x ≔ γ′ ⟨ x ⟩) +ᶜ (δ , x ≔ δ′ ⟨ x ⟩) ≡⟨ PE.sym (update-distrib-+ᶜ γ δ _ _ x) ⟩
    (γ +ᶜ δ , x ≔ γ′ ⟨ x ⟩ + δ′ ⟨ x ⟩)       ≡⟨ cong ((γ +ᶜ δ) , x ≔_) (PE.sym (lookup-distrib-+ᶜ γ′ δ′ x)) ⟩
    (γ +ᶜ δ) , x ≔ ((γ′ +ᶜ δ′) ⟨ x ⟩)        ∎

Conₘ-interchange (var {x₁}) var x = subst₂ _▸_
  (PE.sym (update-self (𝟘ᶜ , x₁ ≔ (Modality.𝟙 𝕄)) x)) refl var

Conₘ-interchange (lamₘ γ▸t) (lamₘ δ▸t) x = lamₘ (Conₘ-interchange γ▸t δ▸t (x +1))

Conₘ-interchange (_∘ₘ_ {γ} {δ = δ} {p = p} γ▸t δ▸u) (_∘ₘ_ {γ′} {δ = δ′} γ′▸t δ′▸u) x =
  subst₂ _▸_ eq refl ((Conₘ-interchange γ▸t γ′▸t x) ∘ₘ (Conₘ-interchange δ▸u δ′▸u x))
  where
  open import Tools.Reasoning.PropositionalEquality
  eq = begin
    (γ , x ≔ (γ′ ⟨ x ⟩)) +ᶜ p ·ᶜ (δ , x ≔ (δ′ ⟨ x ⟩))
       ≡⟨ cong₂ _+ᶜ_ refl (PE.sym (update-distrib-·ᶜ δ p _ x)) ⟩
    (γ , x ≔ (γ′ ⟨ x ⟩)) +ᶜ (p ·ᶜ δ , x ≔ (p · δ′ ⟨ x ⟩))
       ≡⟨ cong₂ _+ᶜ_ refl (cong (_ , x ≔_) (PE.sym (lookup-distrib-·ᶜ δ′ p x))) ⟩
    (γ , x ≔ (γ′ ⟨ x ⟩)) +ᶜ (p ·ᶜ δ , x ≔ ((p ·ᶜ δ′) ⟨ x ⟩))
       ≡⟨ PE.sym (update-distrib-+ᶜ γ _ _ _ x) ⟩
    (γ +ᶜ p ·ᶜ δ) , x ≔ γ′ ⟨ x ⟩ + (p ·ᶜ δ′) ⟨ x ⟩
       ≡⟨ cong (_ , x ≔_) (PE.sym (lookup-distrib-+ᶜ γ′ (p ·ᶜ δ′) x)) ⟩
    (γ +ᶜ p ·ᶜ δ) , x ≔ (γ′ +ᶜ p ·ᶜ δ′) ⟨ x ⟩ ∎

Conₘ-interchange (prodₘ {γ} {δ = δ} γ▸t γ▸t₁ refl) (prodₘ {γ₁} {δ = δ₁} δ▸t δ▸t₁ refl) x = prodₘ
  (Conₘ-interchange γ▸t δ▸t x)
  (Conₘ-interchange γ▸t₁ δ▸t₁ x)
  (subst₂ _≡_ (cong₃ _,_≔_ refl refl
                     (PE.sym (lookup-distrib-+ᶜ γ₁ δ₁ x)))
              (update-distrib-+ᶜ γ δ _ _ x) refl)

Conₘ-interchange (fstₘ γ▸t) (fstₘ δ▸t) x = subst₂ _▸_ (PE.sym (update-self 𝟘ᶜ x)) refl (fstₘ γ▸t)
Conₘ-interchange (sndₘ γ▸t) (sndₘ δ▸t) x = subst₂ _▸_ (PE.sym (update-self 𝟘ᶜ x)) refl (sndₘ γ▸t)

Conₘ-interchange (prodrecₘ {γ} {δ = δ} {p} γ▸t δ▸u) (prodrecₘ {γ′} {δ = δ′} γ′▸t δ′▸u) x =
  subst₂ _▸_ eq refl (prodrecₘ (Conₘ-interchange γ▸t γ′▸t x) (Conₘ-interchange δ▸u δ′▸u (x +1 +1)))
  where
  open import Tools.Reasoning.PropositionalEquality
  eq = begin
     p ·ᶜ (γ , x ≔ (γ′ ⟨ x ⟩)) +ᶜ (δ , x ≔ (δ′ ⟨ x ⟩))
         ≡⟨ cong₂ _+ᶜ_ (PE.sym (update-distrib-·ᶜ γ p _ x)) refl ⟩
     ((p ·ᶜ γ) , x ≔ (p · γ′ ⟨ x ⟩)) +ᶜ (δ , x ≔ (δ′ ⟨ x ⟩))
         ≡⟨ cong₂ _+ᶜ_ (cong (_ , x ≔_) (PE.sym (lookup-distrib-·ᶜ γ′ p x))) refl ⟩
     ((p ·ᶜ γ) , x ≔ ((p ·ᶜ γ′) ⟨ x ⟩)) +ᶜ (δ , x ≔ (δ′ ⟨ x ⟩))
         ≡⟨ PE.sym (update-distrib-+ᶜ (p ·ᶜ γ) δ _ _ x) ⟩
     (p ·ᶜ γ +ᶜ δ) , x ≔ ((p ·ᶜ γ′) ⟨ x ⟩ + δ′ ⟨ x ⟩)
         ≡⟨ cong (_ , x ≔_) (PE.sym (lookup-distrib-+ᶜ (p ·ᶜ γ′) δ′ x)) ⟩
     ((p ·ᶜ γ +ᶜ δ) , x ≔ ((p ·ᶜ γ′ +ᶜ δ′) ⟨ x ⟩)) ∎

Conₘ-interchange zeroₘ zeroₘ x           = subst₂ _▸_ (PE.sym (update-self 𝟘ᶜ x)) refl zeroₘ
Conₘ-interchange (sucₘ γ▸t) (sucₘ δ▸t) x = sucₘ (Conₘ-interchange γ▸t δ▸t x)

Conₘ-interchange (natrecₘ {γ} {p} {r} {δ} γ▸t γ▸t₁ γ▸t₂ r≤0)
                     (natrecₘ {γ₁} {δ = δ₁} δ▸t δ▸t₁ δ▸t₂ r′≤0) x = subst₂ _▸_
                 (PE.trans (cong₂ _·ᶜ_ refl eq)
                           (PE.trans (PE.sym (update-distrib-·ᶜ (γ +ᶜ (p ·ᶜ δ)) _ _ x))
                                     (cong (_ , x ≔_) (PE.sym (lookup-distrib-·ᶜ (γ₁ +ᶜ (p ·ᶜ δ₁)) _ x)))))
                 refl
                 (natrecₘ (Conₘ-interchange γ▸t δ▸t x) (Conₘ-interchange γ▸t₁ δ▸t₁ (x +1 +1))
                 (Conₘ-interchange γ▸t₂ δ▸t₂ x) r≤0)
  where
  open import Tools.Reasoning.PropositionalEquality
  eq = begin
    (γ , x ≔ (γ₁ ⟨ x ⟩)) +ᶜ p ·ᶜ (δ , x ≔ (δ₁ ⟨ x ⟩))
       ≡⟨ cong₂ _+ᶜ_ refl (PE.sym (update-distrib-·ᶜ δ p _ _)) ⟩
    (γ , x ≔ (γ₁ ⟨ x ⟩)) +ᶜ ((p ·ᶜ δ) , x ≔ (p · δ₁ ⟨ x ⟩))
       ≡⟨ cong₂ _+ᶜ_ refl (cong (_ , x ≔_) (PE.sym (lookup-distrib-·ᶜ δ₁ p x))) ⟩
    (γ , x ≔ (γ₁ ⟨ x ⟩)) +ᶜ ((p ·ᶜ δ) , x ≔ ((p ·ᶜ δ₁) ⟨ x ⟩))
       ≡⟨ PE.sym (update-distrib-+ᶜ γ _ _ _ x) ⟩
    (γ +ᶜ p ·ᶜ δ) , x ≔ ((γ₁ ⟨ x ⟩) + ((p ·ᶜ δ₁) ⟨ x ⟩))
       ≡⟨ cong (_ , x ≔_) (PE.sym (lookup-distrib-+ᶜ γ₁ (p ·ᶜ δ₁) x)) ⟩
    (γ +ᶜ p ·ᶜ δ) , x ≔ ((γ₁ +ᶜ p ·ᶜ δ₁) ⟨ x ⟩) ∎

Conₘ-interchange (Emptyrecₘ γ▸t) (Emptyrecₘ δ▸t) x = Emptyrecₘ (Conₘ-interchange γ▸t δ▸t x)
Conₘ-interchange starₘ starₘ x = subst₂ _▸_ (PE.sym (update-self 𝟘ᶜ x)) refl starₘ

-- ⌈ t ⌉ is an upper bound on valid modality contexts
-- If γ ▸ t, then γ ≤ ⌈ t ⌉

thm : γ ≡ δ → γ ≈ᶜ δ
thm eq = subst₂ _≈ᶜ_ refl eq ≈ᶜ-refl

usage-upper-bound : γ ▸ t → γ ≤ᶜ ⌈ t ⌉
usage-upper-bound Uₘ     = ≤ᶜ-refl
usage-upper-bound ℕₘ     = ≤ᶜ-refl
usage-upper-bound Emptyₘ = ≤ᶜ-refl
usage-upper-bound Unitₘ  = ≤ᶜ-refl

usage-upper-bound (Πₘ {δ = δ} {q} {G₁} F G) = +ᶜ-monotone
  (usage-upper-bound F)
  (PE.subst (δ ≈ᶜ_) (tailₘ-distrib-∧ᶜ (δ ∙ q) ⌈ G₁ ⌉) (tailₘ-cong (usage-upper-bound G)))

usage-upper-bound (Σₘ {δ = δ} {q} {G₁} F G) = +ᶜ-monotone
  (usage-upper-bound F)
  (PE.subst (δ ≈ᶜ_) (tailₘ-distrib-∧ᶜ (δ ∙ q) ⌈ G₁ ⌉) (tailₘ-cong (usage-upper-bound G)))

usage-upper-bound var = ≤ᶜ-refl

usage-upper-bound {γ = γ} (lamₘ {p = p} {t₁} t) = PE.subst (γ ≈ᶜ_)
  (tailₘ-distrib-∧ᶜ (γ ∙ p) ⌈ t₁ ⌉)
  (tailₘ-cong (usage-upper-bound t))

usage-upper-bound (t ∘ₘ u) = +ᶜ-monotone
  (usage-upper-bound t)
  (·ᶜ-monotoneʳ (usage-upper-bound u))

usage-upper-bound (prodₘ! t u) = +ᶜ-monotone (usage-upper-bound t) (usage-upper-bound u)
usage-upper-bound (fstₘ t)     = ≤ᶜ-refl
usage-upper-bound (sndₘ t)     = ≤ᶜ-refl

usage-upper-bound (prodrecₘ {γ} {δ = δ} {p} {u = u₁} t u) = +ᶜ-monotone
  (·ᶜ-monotoneʳ (usage-upper-bound t))
  (tailₘ-monotone (tailₘ-monotone (usage-upper-bound u)))

usage-upper-bound zeroₘ    = ≤ᶜ-refl
usage-upper-bound (sucₘ t) = usage-upper-bound t

usage-upper-bound (natrecₘ {γ = γ} {p = p} {r = r} {z = z} {s = s} x x₁ x₂ x₃) = ·ᶜ-monotoneʳ (+ᶜ-monotone le (·ᶜ-monotoneʳ (usage-upper-bound x₂)))
  where
  open import Tools.Reasoning.PartialOrder ≤ᶜ-poset
  le = begin
    γ      ≈˘⟨ ∧ᶜ-idem γ ⟩
    γ ∧ᶜ γ ≤⟨ ∧ᶜ-monotone (usage-upper-bound x)
                          (tailₘ-monotone (tailₘ-monotone
                                          (usage-upper-bound x₁))) ⟩
    ⌈ z ⌉ ∧ᶜ tailₘ (tailₘ ⌈ s ⌉) ∎

usage-upper-bound (Emptyrecₘ e) = usage-upper-bound e
usage-upper-bound starₘ         = ≤ᶜ-refl
usage-upper-bound (sub t x)     = ≤ᶜ-trans x (usage-upper-bound t)


-- A valid modality context can be computed from well typed and well resourced terms
-- If Γ ⊢ t ∷ A and γ ▸ t, then ⌈ t ⌉ ▸ t

usage-calc-term′ : {Γ : Con Term n} {γ : Conₘ n} {t A : Term n}
                 → Γ ⊢ t ∷ A → γ ▸ t → ⌈ t ⌉ ▸ t
usage-calc-term′ (Πⱼ_▹_ {q = q} {G = G} Γ⊢F:U Γ⊢G:U) γ▸t with inv-usage-Π γ▸t
... | invUsageΠΣ δ▸F η▸G _ = Πₘ
      (usage-calc-term′ Γ⊢F:U δ▸F)
      (subst₂ _▸_ (update-head ⌈ G ⌉ q) refl
              (Conₘ-interchange (usage-calc-term′ Γ⊢G:U η▸G) η▸G x0))
usage-calc-term′  (Σⱼ_▹_ {q = q} {G = G} Γ⊢F:U Γ⊢G:U) γ▸t with inv-usage-Σ γ▸t
... | invUsageΠΣ δ▸F η▸G _ = Σₘ
      (usage-calc-term′ Γ⊢F:U δ▸F)
      (subst₂ _▸_ (update-head ⌈ G ⌉ q) refl
              (Conₘ-interchange (usage-calc-term′ Γ⊢G:U η▸G) η▸G x0))
usage-calc-term′ (ℕⱼ x) γ▸t = ℕₘ
usage-calc-term′ (Emptyⱼ x) γ▸t = Emptyₘ
usage-calc-term′ (Unitⱼ x) γ▸t = Unitₘ
usage-calc-term′ (var x x₁) γ▸t = var
usage-calc-term′ (lamⱼ {p = p} {t = t} x Γ⊢t:A) γ▸λt with inv-usage-lam γ▸λt
... | invUsageLam δ▸t _ = lamₘ
      (subst₂ _▸_ (update-head ⌈ t ⌉ p) refl
              (Conₘ-interchange (usage-calc-term′ Γ⊢t:A δ▸t) δ▸t x0))
usage-calc-term′ (Γ⊢t:Π ∘ⱼ Γ⊢u:F) γ▸t with inv-usage-app γ▸t
... | invUsageApp δ▸t η▸u _ =
      (usage-calc-term′ Γ⊢t:Π δ▸t) ∘ₘ (usage-calc-term′ Γ⊢u:F η▸u)
usage-calc-term′ (prodⱼ x x₁ Γ⊢t:A Γ⊢u:B) γ▸t with inv-usage-prod γ▸t
... | invUsageProd δ▸t η▸u _ _ = prodₘ
      (usage-calc-term′ Γ⊢t:A δ▸t)
      (usage-calc-term′ Γ⊢u:B η▸u)
      refl
usage-calc-term′ (fstⱼ x x₁ Γ⊢t:A) γ▸t with inv-usage-fst γ▸t
... | invUsageProj 𝟘▸t _ = fstₘ 𝟘▸t
usage-calc-term′ (sndⱼ x x₁ Γ⊢t:A) γ▸t with inv-usage-snd γ▸t
... | invUsageProj 𝟘▸t _ = sndₘ 𝟘▸t
usage-calc-term′ {n = n} (prodrecⱼ {p = p} {u = u}
                    x x₁ Γ⊢t:Σ x₂ Γ⊢u:A) γ▸t with inv-usage-prodrec γ▸t
... | invUsageProdrec δ▸t η▸u _ = prodrecₘ
      (usage-calc-term′ Γ⊢t:Σ δ▸t)
      (subst₂ _▸_ eq refl (Conₘ-interchange (Conₘ-interchange
                          (usage-calc-term′ Γ⊢u:A η▸u) η▸u (x0 +1)) η▸u x0))
  where
  open import Tools.Reasoning.PropositionalEquality
  γu : Conₘ (1+ (1+ n))
  γu = ⌈ u ⌉
  eq =  begin
     ((γu , x0 +1 ≔ p) , x0 ≔ p)
       ≡⟨ cong₂ (_,_≔ p) (update-step γu p x0) refl ⟩
     (( (tailₘ γu , x0 ≔ p) ∙ headₘ γu) , x0 ≔ p)
       ≡⟨ cong (_, x0 ≔ p) (cong (_∙ p) (update-head (tailₘ γu) p)) ⟩
     ((tailₘ (tailₘ γu) ∙ p ∙ headₘ γu) , x0 ≔ p)
       ≡⟨ update-head ((tailₘ (tailₘ γu) ∙ p) ∙ headₘ γu) p ⟩
     (tailₘ (tailₘ γu) ∙ p ∙ p) ∎

usage-calc-term′ (zeroⱼ x) γ▸t = zeroₘ
usage-calc-term′ (sucⱼ Γ⊢t:ℕ) γ▸t  with inv-usage-suc γ▸t
... | invUsageSuc δ▸t _ = sucₘ (usage-calc-term′ Γ⊢t:ℕ δ▸t)

usage-calc-term′ {n = n} (natrecⱼ {p = p} {r = r} {s = s} {z = z}
                 x Γ⊢z:G Γ⊢s:G Γ⊢n:ℕ) γ▸t with inv-usage-natrec γ▸t
... | invUsageNatrec {δ = δ} δ▸z δ▸s η▸n r≤0 _ = natrecₘ
  (sub (usage-calc-term′ Γ⊢z:G δ▸z) (∧ᶜ-decreasingˡ ⌈ z ⌉ (tailₘ (tailₘ ⌈ s ⌉))))
  (sub (Conₘ-interchange (Conₘ-interchange
                         (usage-calc-term′ Γ⊢s:G δ▸s) δ▸s (x0 +1)) δ▸s x0)
       le)
       -- (subst₂ _≤ᶜ_ refl (PE.sym eq)
       --         (cong₂ _∙_ (cong₂ _∙_ (∧ᶜ-decreasingʳ ⌈ z ⌉ (tailₘ (tailₘ ⌈ s ⌉)))
       --                (≤-refl {𝕄 = 𝕄}) ) (≤-refl {𝕄 = 𝕄}))))
  (usage-calc-term′ Γ⊢n:ℕ η▸n)
  r≤0
  where
  open import Tools.Reasoning.PartialOrder ≤ᶜ-poset
  le = begin
    (⌈ z ⌉ ∧ᶜ tailₘ (tailₘ ⌈ s ⌉)) ∙ p ∙ r
       ≤⟨ ∙-monotoneˡ (∙-monotoneˡ (∧ᶜ-decreasingʳ ⌈ z ⌉ (tailₘ (tailₘ ⌈ s ⌉)))) ⟩
    (tailₘ (tailₘ ⌈ s ⌉)) ∙ p ∙ r
       ≡˘⟨ update-head (tailₘ (tailₘ ⌈ s ⌉) ∙ p ∙ headₘ ⌈ s ⌉) r ⟩
    (tailₘ (tailₘ ⌈ s ⌉) ∙ p ∙ headₘ ⌈ s ⌉) , x0 ≔ r
      ≡˘⟨ cong (_, x0 ≔ r) (cong (_∙ p) (update-head (tailₘ ⌈ s ⌉) p)) ⟩
    (((tailₘ ⌈ s ⌉) , x0 ≔ p) ∙ headₘ ⌈ s ⌉) , x0 ≔ r
      ≡˘⟨ cong (_, x0 ≔ r) (update-step ⌈ s ⌉ p x0) ⟩
    ((⌈ s ⌉ , (x0 +1) ≔ p) , x0 ≔ r)
      ≡⟨⟩
    (⌈ s ⌉ , (x0 +1) ≔ ((δ ∙ p ∙ r) ⟨ x0 +1 ⟩)) , x0 ≔ ((δ ∙ p ∙ r) ⟨ x0 ⟩) ∎

usage-calc-term′ (Emptyrecⱼ x Γ⊢t:A) γ▸t with inv-usage-Emptyrec γ▸t
... | invUsageEmptyrec δ▸t _ = Emptyrecₘ (usage-calc-term′ Γ⊢t:A δ▸t)
usage-calc-term′ (starⱼ x) γ▸t = starₘ
usage-calc-term′ (conv Γ⊢t:A x) γ▸t = usage-calc-term′ Γ⊢t:A γ▸t

-- A valid modality context can be computed from well typed and well resourced terms
-- If Γ ⊢ γ ▸ t ∷ A ◂ δ, then ⌈ t ⌉ ▸ t

usage-calc-term : Γ ⊢ γ ▸ t ∷ A ◂ γ′ → ⌈ t ⌉ ▸ t
usage-calc-term (Γ⊢t:A , γ▸t , γ′▸A) = usage-calc-term′ Γ⊢t:A γ▸t


-- A valid modality context can be computed from well typed and well resourced types
-- If Γ ⊢ A ◂ γ, then ⌈ A ⌉ ▸ A

usage-calc-type : Γ ⊢ A ◂ γ → ⌈ A ⌉ ▸ A
usage-calc-type (Uⱼ x , γ▸A) = Uₘ
usage-calc-type (ℕⱼ x , γ▸A) = ℕₘ
usage-calc-type (Emptyⱼ x , γ▸A) = Emptyₘ
usage-calc-type (Unitⱼ x , γ▸A) = Unitₘ
usage-calc-type (Πⱼ_▹_ {G = G} {q = q} Γ⊢F Γ⊢G , γ▸Π) with inv-usage-Π γ▸Π
... | invUsageΠΣ δ▸F η▸G _ = Πₘ
      (usage-calc-type (Γ⊢F , δ▸F))
      (subst₂ _▸_ (update-head ⌈ G ⌉ q) refl
                  (Conₘ-interchange (usage-calc-type (Γ⊢G , η▸G)) η▸G x0))
usage-calc-type (Σⱼ_▹_ {G = G} {q = q} Γ⊢F Γ⊢G , γ▸Σ) with inv-usage-Σ γ▸Σ
... | invUsageΠΣ δ▸F η▸G _ = Σₘ
      (usage-calc-type (Γ⊢F , δ▸F))
      (subst₂ _▸_ (update-head ⌈ G ⌉ q) refl
                  (Conₘ-interchange (usage-calc-type (Γ⊢G , η▸G)) η▸G x0))
usage-calc-type (univ Γ⊢A:U , γ▸A) = usage-calc-term′ Γ⊢A:U γ▸A
