{-# OPTIONS --without-K --safe #-}
module Definition.Modality.Substitution.Properties where

open import Definition.Modality
open import Definition.Modality.Context
open import Definition.Modality.Context.Properties
open import Definition.Modality.Substitution
open import Definition.Modality.Usage
open import Definition.Modality.Usage.Weakening
open import Definition.Untyped as U

open import Tools.Fin
open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality as PE

private
  variable
    M : Set
    𝕄 : Modality M
    m n : Nat
    γ δ η : Conₘ 𝕄 n
    t u u′ : Term M n
    σ : Subst M m n
    p q : M

-- Linearity proerties of *>

*>-linear-+ᶜ : {𝕄 : Modality M} (Ψ : Substₘ 𝕄 m n) (γ δ : Conₘ 𝕄 n) → Ψ *> (γ +ᶜ δ) ≡ Ψ *> γ +ᶜ Ψ *> δ
*>-linear-+ᶜ           ε       ε       ε      = PE.sym (+ᶜ-identityˡ 𝟘ᶜ)
*>-linear-+ᶜ {𝕄 = 𝕄} (Ψ ∙ η) (γ ∙ p) (δ ∙ q) = begin
  Ψ ∙ η *> (γ ∙ p +ᶜ δ ∙ q)                       ≡⟨ cong₂ _+ᶜ_ refl (*>-linear-+ᶜ Ψ γ δ) ⟩
  (Modality._+_ 𝕄 p q) ·ᶜ η +ᶜ Ψ *> γ +ᶜ Ψ *> δ  ≡⟨ cong₂ _+ᶜ_ (·ᶜ-distribʳ-+ᶜ p q η) refl ⟩
  (p ·ᶜ η +ᶜ q ·ᶜ η) +ᶜ Ψ *> γ +ᶜ Ψ *> δ          ≡⟨ cong₂ _+ᶜ_ refl (+ᶜ-comm (Ψ *> γ) (Ψ *> δ)) ⟩
  (p ·ᶜ η +ᶜ q ·ᶜ η) +ᶜ Ψ *> δ +ᶜ Ψ *> γ          ≡⟨ +ᶜ-assoc (p ·ᶜ η) (q ·ᶜ η) (Ψ *> δ +ᶜ Ψ *> γ) ⟩
  p ·ᶜ η +ᶜ q ·ᶜ η +ᶜ Ψ *> δ +ᶜ Ψ *> γ            ≡⟨ +ᶜ-comm (p ·ᶜ η) (q ·ᶜ η +ᶜ Ψ *> δ +ᶜ Ψ *> γ) ⟩
  (q ·ᶜ η +ᶜ Ψ *> δ +ᶜ Ψ *> γ) +ᶜ p ·ᶜ η          ≡⟨  +ᶜ-assoc _ _ _ ⟩
  q ·ᶜ η +ᶜ (Ψ *> δ +ᶜ Ψ *> γ) +ᶜ p ·ᶜ η          ≡⟨ cong₂ _+ᶜ_ refl (+ᶜ-assoc _ _ _) ⟩
  q ·ᶜ η +ᶜ Ψ *> δ +ᶜ Ψ *> γ +ᶜ p ·ᶜ η            ≡⟨ sym (+ᶜ-assoc _ _ _) ⟩
  (q ·ᶜ η +ᶜ Ψ *> δ) +ᶜ Ψ *> γ +ᶜ p ·ᶜ η          ≡⟨ cong₂ _+ᶜ_ refl (+ᶜ-comm _ _) ⟩
  (q ·ᶜ η +ᶜ Ψ *> δ) +ᶜ p ·ᶜ η +ᶜ Ψ *> γ          ≡⟨ +ᶜ-comm _ _ ⟩
  ((p ·ᶜ η +ᶜ Ψ *> γ) +ᶜ q ·ᶜ η +ᶜ Ψ *> δ)        ∎

*>-linear-·ᶜ : (Ψ : Substₘ 𝕄 m n) (p : M) (γ : Conₘ 𝕄 n) → Ψ *> (p ·ᶜ γ) ≡ p ·ᶜ (Ψ *> γ)
*>-linear-·ᶜ  ε p ε = PE.sym (·ᶜ-zeroʳ p)
*>-linear-·ᶜ {𝕄 = 𝕄} (Ψ ∙ δ) p (γ ∙ q) = begin
  (Modality._·_ 𝕄 p q) ·ᶜ δ +ᶜ Ψ *> (p ·ᶜ γ) ≡⟨ cong₂ _+ᶜ_
                                                      (·ᶜ-assoc p q δ)
                                                      (*>-linear-·ᶜ Ψ p γ)
                                               ⟩
  p ·ᶜ (q ·ᶜ δ) +ᶜ p ·ᶜ (Ψ *> γ)              ≡⟨ sym (·ᶜ-distribˡ-+ᶜ p (q ·ᶜ δ) (Ψ *> γ)) ⟩
  p ·ᶜ (q ·ᶜ δ +ᶜ Ψ *> γ)                     ∎

*>-linear : (Ψ : Substₘ 𝕄 m n) (p q : M) (γ δ : Conₘ 𝕄 n)
          → Ψ *> (p ·ᶜ γ +ᶜ q ·ᶜ δ) ≡ p ·ᶜ Ψ *> γ +ᶜ q ·ᶜ Ψ *> δ
*>-linear Ψ p q γ δ = begin
  Ψ *> (p ·ᶜ γ +ᶜ q ·ᶜ δ)        ≡⟨ *>-linear-+ᶜ Ψ (p ·ᶜ γ) (q ·ᶜ δ) ⟩
  Ψ *> (p ·ᶜ γ) +ᶜ Ψ *> (q ·ᶜ δ) ≡⟨ cong₂ _+ᶜ_ (*>-linear-·ᶜ Ψ p γ)
                                               (*>-linear-·ᶜ Ψ q δ) ⟩
  (p ·ᶜ Ψ *> γ +ᶜ q ·ᶜ Ψ *> δ)   ∎

-- Other properties of modality substitutions

*>-zeroʳ : (Ψ : Substₘ 𝕄 m n) → substₘ Ψ 𝟘ᶜ ≡ 𝟘ᶜ
*>-zeroʳ ε = refl
*>-zeroʳ (Ψ ∙ γ) = PE.subst (_≡ 𝟘ᶜ)
  (cong₂ _+ᶜ_ (PE.sym (·ᶜ-zeroˡ γ))
         (PE.sym (*>-zeroʳ Ψ)))
  (+ᶜ-identityˡ 𝟘ᶜ)

*>-monotone : {γ δ : Conₘ 𝕄 n} (Ψ : Substₘ 𝕄 m n) → γ ≤ᶜ δ → Ψ *> γ ≤ᶜ Ψ *> δ
*>-monotone {γ = ε}     {ε}      ε      γ≤δ = ≤ᶜ-reflexive
*>-monotone {γ = γ ∙ p} {δ ∙ q} (Ψ ∙ η) γ≤δ = +ᶜ-monotone₂
  (·ᶜ-monotone₂ ≤ᶜ-reflexive (cong headₘ γ≤δ))
  (*>-monotone Ψ (cong tailₘ γ≤δ))

-- Properties of specific substitutions

wk1Substₘ-app : (Ψ : Substₘ 𝕄 m n) (γ : Conₘ 𝕄 n) → wk1Substₘ Ψ *> γ ≡ (Ψ *> γ) ∙ (Modality.𝟘 𝕄)
wk1Substₘ-app ε ε = refl
wk1Substₘ-app {𝕄 = 𝕄} (Ψ ∙ δ) (γ ∙ p) = begin
  (p ·ᶜ δ) ∙ (Modality._·_ 𝕄 p (Modality.𝟘 𝕄)) +ᶜ wk1Substₘ Ψ *> γ
    ≡⟨ cong₂ _+ᶜ_ (cong₂ _∙_ refl (proj₂ (Modality.·-Zero 𝕄) p))
                  (wk1Substₘ-app Ψ γ) ⟩
  (p ·ᶜ δ +ᶜ Ψ *> γ) ∙ (𝕄 Modality.+ Modality.𝟘 𝕄) (Modality.𝟘 𝕄)
    ≡⟨  cong₂ _∙_ refl (proj₁ (Modality.+-Identity 𝕄) (Modality.𝟘 𝕄)) ⟩
  ((p ·ᶜ δ +ᶜ Ψ *> γ) ∙ Modality.𝟘 𝕄) ∎


liftSubstₘ-app : (Ψ : Substₘ 𝕄 m n) (γ : Conₘ 𝕄 n) (p : M)
               → liftSubstₘ Ψ *> (γ ∙ p) ≡ (Ψ *> γ) ∙ p
liftSubstₘ-app {𝕄 = 𝕄} ε ε p = cong₂ _∙_ (sym γ′) (sym p′)
  where
  γ′ = begin
    𝟘ᶜ            ≡⟨ sym (·ᶜ-zeroʳ p) ⟩
    p ·ᶜ 𝟘ᶜ       ≡⟨ sym (+ᶜ-identityʳ (p ·ᶜ 𝟘ᶜ)) ⟩
    p ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ ∎
  p′ = begin
    p                                 ≡⟨ sym (proj₂ (Modality.·-Identity 𝕄) p) ⟩
    Modality._·_ 𝕄 p (Modality.𝟙 𝕄)  ≡⟨ sym (proj₂ (Modality.+-Identity 𝕄) _) ⟩
    ((𝕄 Modality.+ (𝕄 Modality.· p) (Modality.𝟙 𝕄)) (Modality.𝟘 𝕄)) ∎
liftSubstₘ-app {𝕄 = 𝕄} (Ψ ∙ x) γ p = begin
  (p ·ᶜ 𝟘ᶜ) ∙ (Modality._·_ 𝕄 p (Modality.𝟙 𝕄))
    +ᶜ (wk1Substₘ Ψ ∙ (x ∙ Modality.𝟘 𝕄)) *> γ
      ≡⟨ cong₂ _+ᶜ_ (cong₂ _∙_ (·ᶜ-zeroʳ p) (proj₂ (Modality.·-Identity 𝕄) p))
                    (wk1Substₘ-app (Ψ ∙ x) γ) ⟩
  (𝟘ᶜ +ᶜ (Ψ ∙ x) *> γ) ∙ (𝕄 Modality.+ p) (Modality.𝟘 𝕄)
      ≡⟨ cong₂ _∙_ (+ᶜ-identityˡ ((Ψ ∙ x) *> γ)) (proj₂ (Modality.+-Identity 𝕄) p) ⟩
  (((Ψ ∙ x) *> γ) ∙ p) ∎


idSubstₘ-LeftIdentity : (γ : Conₘ 𝕄 n) → idSubstₘ *> γ ≡ γ
idSubstₘ-LeftIdentity           ε      = refl
idSubstₘ-LeftIdentity {𝕄 = 𝕄} (γ ∙ p) = begin
  (p ·ᶜ 𝟘ᶜ) ∙ (𝕄 Modality.· p) (Modality.𝟙 𝕄) +ᶜ wk1Substₘ idSubstₘ *> γ
    ≡⟨ cong₂ _+ᶜ_ (cong₂ _∙_ (·ᶜ-zeroʳ p) (proj₂ (Modality.·-Identity 𝕄) p)) (wk1Substₘ-app idSubstₘ γ) ⟩
  (𝟘ᶜ +ᶜ idSubstₘ *> γ) ∙ (𝕄 Modality.+ p) (Modality.𝟘 𝕄)
    ≡⟨ cong₂ _∙_ (+ᶜ-identityˡ (idSubstₘ *> γ)) (proj₂ (Modality.+-Identity 𝕄) p) ⟩
  (idSubstₘ *> γ) ∙ p ≡⟨ cong (_∙ p) (idSubstₘ-LeftIdentity γ) ⟩
  (γ ∙ p) ∎


-- Well-formedness of substitutions

wf-sgSubstₘ : γ ▸ u → sgSubstₘ γ ▶ sgSubst u
wf-sgSubstₘ {γ = γ} γ▸u x0 = subst₂ _▸_
  (PE.subst (γ ≡_)
            (cong₂ _+ᶜ_ (PE.sym (·ᶜ-identityˡ _))
                        (PE.sym (idSubstₘ-LeftIdentity _)))
            (PE.sym (+ᶜ-identityʳ γ))) refl γ▸u
wf-sgSubstₘ γ▸u (x +1) = PE.subst (_▸ var x)
  (subst₂ _≡_ (+ᶜ-identityˡ _)
          (cong₂ _+ᶜ_ (PE.sym (·ᶜ-zeroˡ _))
                      (PE.sym (idSubstₘ-LeftIdentity _))) refl) var


wf-wk1Substₘ : (Ψ : Substₘ 𝕄 m n) (σ : Subst M m n) → Ψ ▶ σ → wk1Substₘ Ψ ▶ wk1Subst σ
wf-wk1Substₘ Ψ σ Ψ▶σ x = subst₂ _▸_ (sym (wk1Substₘ-app Ψ _)) refl (wk1-usage (Ψ▶σ x))

wf-liftSubstₘ : {Ψ : Substₘ 𝕄 m n} → Ψ ▶ σ → liftSubstₘ Ψ ▶ liftSubst σ
wf-liftSubstₘ {𝕄 = 𝕄} {Ψ = Ψ} Ψ▶σ x0 = PE.subst (_▸ var x0)
  (cong₂ _+ᶜ_
    (cong₂ _∙_
      (sym (·ᶜ-identityˡ _))
      (sym (proj₁ (Modality.·-Identity 𝕄) (Modality.𝟙 𝕄)))
    )
    (sym (*>-zeroʳ (wk1Substₘ Ψ)))
  )
  (PE.subst (_▸ var x0)
    (cong₂ _∙_
      (sym (+ᶜ-identityʳ _))
      (sym (proj₂ (Modality.+-Identity 𝕄) (Modality.𝟙 𝕄)))
    )
  var
  )
wf-liftSubstₘ {𝕄 = 𝕄} {Ψ = Ψ} Ψ▶σ (_+1 x) =
  subst₂ _▸_ wkΨ*>≡ refl (wf-wk1Substₘ Ψ _ Ψ▶σ x)
  where
  wkΨ*>≡ = begin
   wk1Substₘ Ψ *> (𝟘ᶜ , x ≔ Modality.𝟙 𝕄)
     ≡⟨ sym (+ᶜ-identityˡ _ ) ⟩
   𝟘ᶜ +ᶜ wk1Substₘ Ψ *> (𝟘ᶜ , x ≔ Modality.𝟙 𝕄)
     ≡⟨ cong₂ _+ᶜ_ (cong₂ _∙_ (sym (·ᶜ-zeroˡ 𝟘ᶜ))
        (sym (proj₁ (Modality.·-Zero 𝕄) (Modality.𝟙 𝕄)))) refl ⟩
   (Modality.𝟘 𝕄 ·ᶜ 𝟘ᶜ) ∙ (𝕄 Modality.· Modality.𝟘 𝕄) (Modality.𝟙 𝕄)
      +ᶜ wk1Substₘ Ψ *> (𝟘ᶜ , x ≔ Modality.𝟙 𝕄) ∎


wf-consSubstₘ : {𝕄 : Modality M} {Ψ : Substₘ 𝕄 m n} {γ : Conₘ 𝕄 m}
             → Ψ ▶ σ → γ ▸ t → Ψ ∙ γ ▶ consSubst σ t
wf-consSubstₘ {𝕄 = 𝕄} {Ψ = Ψ} {γ = γ} Ψ▶σ γ▸t x0 = subst₂ _▸_ γ≡ refl γ▸t
  where
  γ≡ = begin
       γ                             ≡⟨ sym (+ᶜ-identityʳ _) ⟩
       γ +ᶜ 𝟘ᶜ                       ≡⟨ cong₂ _+ᶜ_ (sym (·ᶜ-identityˡ _)) (sym (*>-zeroʳ Ψ)) ⟩
       Modality.𝟙 𝕄 ·ᶜ γ +ᶜ Ψ *> 𝟘ᶜ ∎
wf-consSubstₘ {𝕄 = 𝕄} {Ψ = Ψ} {γ = γ} Ψ▶σ γ▸t (x +1) = subst₂ _▸_ Ψ*>≡ refl (Ψ▶σ x)
  where
  Ψ*>≡ = begin
         Ψ *> (𝟘ᶜ , x ≔ Modality.𝟙 𝕄)                       ≡⟨ sym (+ᶜ-identityˡ _) ⟩
         𝟘ᶜ +ᶜ Ψ *> (𝟘ᶜ , x ≔ Modality.𝟙 𝕄)                 ≡⟨ cong₂ _+ᶜ_ (sym (·ᶜ-zeroˡ _)) refl ⟩
         Modality.𝟘 𝕄 ·ᶜ γ +ᶜ Ψ *> (𝟘ᶜ , x ≔ Modality.𝟙 𝕄) ∎


-- Substitution lemma for modalities

substₘ-lemma : (Ψ : Substₘ 𝕄 m n) (σ : Subst M m n) → Ψ ▶ σ → γ ▸ t → substₘ Ψ γ ▸ U.subst σ t
substₘ-lemma Ψ σ Ψ▶σ Uₘ     = PE.subst (_▸ U)     (PE.sym (*>-zeroʳ Ψ)) Uₘ
substₘ-lemma Ψ σ Ψ▶σ ℕₘ     = PE.subst (_▸ ℕ)     (PE.sym (*>-zeroʳ Ψ)) ℕₘ
substₘ-lemma Ψ σ Ψ▶σ Emptyₘ = PE.subst (_▸ Empty) (PE.sym (*>-zeroʳ Ψ)) Emptyₘ
substₘ-lemma Ψ σ Ψ▶σ Unitₘ  = PE.subst (_▸ Unit)  (PE.sym (*>-zeroʳ Ψ)) Unitₘ

substₘ-lemma Ψ σ Ψ▶σ (Πₘ γ▸F δ▸G) = subst₂ _▸_ (PE.sym (*>-linear-+ᶜ Ψ _ _)) refl (Πₘ γ▸F′ δ▸G″)
  where
  γ▸F′ = substₘ-lemma Ψ σ Ψ▶σ γ▸F
  Ψ′   = liftSubstₘ Ψ
  δ▸G′ = substₘ-lemma (liftSubstₘ Ψ) (liftSubst σ) (wf-liftSubstₘ Ψ▶σ) δ▸G
  δ▸G″ = subst₂ _▸_ (liftSubstₘ-app Ψ _ _) refl δ▸G′

substₘ-lemma Ψ σ Ψ▶σ (Σₘ γ▸F δ▸G) = subst₂ _▸_ (PE.sym (*>-linear-+ᶜ Ψ _ _)) refl (Σₘ γ▸F′ δ▸G″)
  where
  γ▸F′ = substₘ-lemma Ψ σ Ψ▶σ γ▸F
  Ψ′   = liftSubstₘ Ψ
  δ▸G′ = substₘ-lemma (liftSubstₘ Ψ) (liftSubst σ) (wf-liftSubstₘ Ψ▶σ) δ▸G
  δ▸G″ = subst₂ _▸_ (liftSubstₘ-app Ψ _ _) refl δ▸G′

substₘ-lemma Ψ σ Ψ▶σ (var {x}) = Ψ▶σ x

substₘ-lemma Ψ σ Ψ▶σ (lamₘ γ▸t) = lamₘ (subst₂ _▸_ (liftSubstₘ-app Ψ _ _) refl γ▸t′)
  where
  γ▸t′ = (substₘ-lemma (liftSubstₘ Ψ) (liftSubst σ) (wf-liftSubstₘ Ψ▶σ) γ▸t)

substₘ-lemma Ψ σ Ψ▶σ (γ▸t ∘ₘ δ▸u) = subst₂ _▸_
  (subst₂ _≡_ (cong₂ _+ᶜ_ refl (*>-linear-·ᶜ Ψ _ _)) (sym (*>-linear-+ᶜ Ψ _ _)) refl)
  refl
  ((substₘ-lemma Ψ σ Ψ▶σ γ▸t) ∘ₘ (substₘ-lemma Ψ σ Ψ▶σ δ▸u))


substₘ-lemma Ψ σ Ψ▶σ (prodₘ {γ = γ} {δ = δ} γ▸t δ▸u PE.refl) = subst₂ _▸_
  (PE.sym (*>-linear-+ᶜ Ψ γ δ))
  refl
  (prodₘ! (substₘ-lemma Ψ σ Ψ▶σ γ▸t) (substₘ-lemma Ψ σ Ψ▶σ δ▸u))

substₘ-lemma Ψ σ Ψ▶σ (fstₘ γ▸t) = subst₂ _▸_
  (PE.sym (*>-zeroʳ Ψ))
  refl
  (fstₘ (subst₂ _▸_ (*>-zeroʳ Ψ) refl (substₘ-lemma Ψ σ Ψ▶σ γ▸t)))

substₘ-lemma Ψ σ Ψ▶σ (sndₘ γ▸t) =  subst₂ _▸_
  (PE.sym (*>-zeroʳ Ψ))
  refl
  (sndₘ (subst₂ _▸_ (*>-zeroʳ Ψ) refl (substₘ-lemma Ψ σ Ψ▶σ γ▸t)))

substₘ-lemma {𝕄 = 𝕄} Ψ σ Ψ▶σ (prodrecₘ {γ = γ} {δ = δ} {p} γ▸t δ▸u) = subst₂ _▸_
  --(PE.sym (*>-linear-+ᶜ {!!} {!!} {!!}))
  (subst₂ _≡_ (cong₂ _+ᶜ_ (*>-linear-·ᶜ Ψ p γ) refl) (sym (*>-linear-+ᶜ Ψ (p ·ᶜ γ) δ)) refl)
  refl
  (prodrecₘ (substₘ-lemma Ψ σ Ψ▶σ γ▸t) δ▸u″)
  where
  δ▸u′ = substₘ-lemma (liftSubstₘ (liftSubstₘ Ψ)) (liftSubst (liftSubst σ)) (wf-liftSubstₘ (wf-liftSubstₘ Ψ▶σ)) δ▸u
  eq = begin
    (liftSubstₘ (liftSubstₘ Ψ)) *> (δ ∙ p ∙ p)
      ≡⟨ liftSubstₘ-app (liftSubstₘ Ψ) (δ ∙ p) p ⟩
    ((p ·ᶜ 𝟘ᶜ) ∙ (Modality._·_ 𝕄 p (Modality.𝟙 𝕄)) +ᶜ wk1Substₘ Ψ *> δ) ∙ p
      ≡⟨ cong₂ _∙_ (cong₂ _+ᶜ_ (cong₂ _∙_ (·ᶜ-zeroʳ p)
             (proj₂ (Modality.·-Identity 𝕄) p)) (wk1Substₘ-app Ψ δ)) refl ⟩
    _ ≡⟨ cong₂ _∙_ (cong₂ _∙_ (+ᶜ-identityˡ _) (proj₂ (Modality.+-Identity 𝕄) p)) refl ⟩
    _ ∎
  δ▸u″ = subst₂ _▸_ eq refl δ▸u′

substₘ-lemma Ψ σ Ψ▶σ zeroₘ =  PE.subst (_▸ zero) (PE.sym (*>-zeroʳ Ψ)) zeroₘ

substₘ-lemma Ψ σ Ψ▶σ (sucₘ γ▸t) = sucₘ (substₘ-lemma Ψ σ Ψ▶σ γ▸t)

substₘ-lemma {𝕄 = 𝕄} Ψ σ Ψ▶σ (natrecₘ {γ} {p = p} {r = r} {δ} γ▸z γ▸s δ▸n)
  = subst₂ _▸_ eq refl (natrecₘ γ▸z′ γ▸s″ δ▸n′ )
  where
  γ▸z′ = substₘ-lemma Ψ σ Ψ▶σ γ▸z
  γ▸s′ = substₘ-lemma (liftSubstₘ (liftSubstₘ Ψ)) (liftSubst (liftSubst σ)) (wf-liftSubstₘ (wf-liftSubstₘ Ψ▶σ)) γ▸s
  δ▸n′ = substₘ-lemma Ψ σ Ψ▶σ δ▸n
  eq′ = begin
      liftSubstₘ (liftSubstₘ Ψ) *> (γ ∙ p ∙ r)
        ≡⟨ liftSubstₘ-app (liftSubstₘ Ψ) (γ ∙ p) r ⟩
      ((p ·ᶜ 𝟘ᶜ) ∙ (Modality._·_ 𝕄 p (Modality.𝟙 𝕄)) +ᶜ wk1Substₘ Ψ *> γ) ∙ r
        ≡⟨ cong (_∙ r) (cong₂ _+ᶜ_ (cong₂ _∙_ (·ᶜ-zeroʳ p)
                       (proj₂ (Modality.·-Identity 𝕄) p)) (wk1Substₘ-app Ψ γ)) ⟩
      (𝟘ᶜ +ᶜ Ψ *> γ) ∙ (Modality._+_ 𝕄 p (Modality.𝟘 𝕄)) ∙ r
        ≡⟨ cong (_∙ r) (cong₂ _∙_ (+ᶜ-identityˡ (Ψ *> γ))
                       (proj₂ (Modality.+-Identity 𝕄) p)) ⟩
      (Ψ *> γ) ∙ p ∙ r ∎
  γ▸s″ = subst₂ _▸_ eq′ refl γ▸s′
  eq = begin
     (𝕄 Modality.*) r ·ᶜ (substₘ Ψ γ +ᶜ p ·ᶜ substₘ Ψ δ)
       ≡⟨ cong₂ _·ᶜ_ refl (cong₂ _+ᶜ_ refl (sym (*>-linear-·ᶜ Ψ p δ))) ⟩
     _ ≡⟨ cong₂ _·ᶜ_ refl (sym (*>-linear-+ᶜ Ψ γ (p ·ᶜ δ))) ⟩
     _ ≡⟨ sym (*>-linear-·ᶜ Ψ _ _) ⟩
     (Ψ *> (((Modality._* 𝕄 r) ·ᶜ (γ +ᶜ p ·ᶜ δ)))) ∎

substₘ-lemma Ψ σ Ψ▶σ (Emptyrecₘ γ▸t) = Emptyrecₘ (substₘ-lemma Ψ σ Ψ▶σ γ▸t)
substₘ-lemma Ψ σ Ψ▶σ starₘ           = PE.subst (_▸ star) (PE.sym (*>-zeroʳ Ψ)) starₘ
substₘ-lemma Ψ σ Ψ▶σ (sub γ▸t x)     = sub (substₘ-lemma Ψ σ Ψ▶σ γ▸t) (*>-monotone Ψ x)

sgSubstₘ-lemma : γ ∙ p ▸ t → δ ▸ u → (γ +ᶜ p ·ᶜ δ) ▸ t [ u ]
sgSubstₘ-lemma {γ = γ} {p} {δ = δ} γ▸t δ▸u = subst₂ _▸_ eq refl
  (substₘ-lemma (sgSubstₘ _) (sgSubst _) (wf-sgSubstₘ δ▸u) γ▸t)
  where
  eq = begin
    (idSubstₘ ∙ δ) *> (γ ∙ p) ≡⟨ +ᶜ-comm _ _ ⟩
    idSubstₘ *> γ +ᶜ p ·ᶜ δ   ≡⟨ cong₂ _+ᶜ_ (idSubstₘ-LeftIdentity γ) refl ⟩
    γ +ᶜ p ·ᶜ δ               ∎

doubleSubstₘ-lemma : γ ∙ q ∙ p ▸ t → δ ▸ u → η ▸ u′ → (γ +ᶜ p ·ᶜ δ +ᶜ q ·ᶜ η) ▸ t [ u ][ u′ ]
doubleSubstₘ-lemma {γ = γ} {q} {p} {δ = δ} {η = η} γ▸t δ▸u η▸u′ = subst₂ _▸_ eq refl
  (substₘ-lemma (consSubstₘ (sgSubstₘ _) _) _
                (wf-consSubstₘ (wf-sgSubstₘ η▸u′) δ▸u) γ▸t)
  where
  eq = begin
    p ·ᶜ δ +ᶜ q ·ᶜ η +ᶜ idSubstₘ *> γ ≡⟨ cong₂ _+ᶜ_ refl (cong₂ _+ᶜ_ refl (idSubstₘ-LeftIdentity γ)) ⟩
    p ·ᶜ δ +ᶜ q ·ᶜ η +ᶜ γ             ≡⟨ sym (+ᶜ-assoc (p ·ᶜ δ) (q ·ᶜ η) γ) ⟩
    (p ·ᶜ δ +ᶜ q ·ᶜ η) +ᶜ γ           ≡⟨ +ᶜ-comm (p ·ᶜ δ +ᶜ q ·ᶜ η) γ ⟩
    γ +ᶜ p ·ᶜ δ +ᶜ q ·ᶜ η             ∎
