{-# OPTIONS --without-K --allow-unsolved-metas #-}

open import Tools.Relation
open import Definition.Modality

module Definition.Modality.Substitution.Properties
  {M : Set} {_≈_ : Rel M _}
  (𝕄 : Modality M _≈_)
  where

open import Definition.Modality.Context 𝕄
open import Definition.Modality.Context.Properties 𝕄
open import Definition.Modality.Substitution 𝕄
open import Definition.Modality.Usage 𝕄
open import Definition.Modality.Usage.Properties 𝕄
open import Definition.Modality.Usage.Weakening 𝕄
open import Definition.Typed 𝕄 using (_⊢_∷_)
open import Definition.Untyped M _≈_ as U hiding (ε ; _∙_)

open import Tools.Fin
open import Tools.Nat hiding (_+_)
open import Tools.Product
open import Tools.PropositionalEquality as PE

open Modality 𝕄

private
  variable
    ℓ m n : Nat
    γ δ η : Conₘ n
    t u u′ : Term n
    σ : Subst m n
    p q : M

----------------------
-- Properties of *> --
----------------------

-- Modality substitution application distributes over addition.
-- Ψ *> (γ +ᶜ δ) ≡ Ψ *> γ +ᶜ Ψ *> δ.
-- Proof by induciton on Ψ using identiy, commutativity and associtivity of addition
-- and distributivity of multiplication over addition.

*>-distrib-+ᶜ : (Ψ : Substₘ m n) (γ δ : Conₘ n) → Ψ *> (γ +ᶜ δ) ≈ᶜ Ψ *> γ +ᶜ Ψ *> δ
*>-distrib-+ᶜ []       ε       ε      = ≈ᶜ-sym (+ᶜ-identityˡ 𝟘ᶜ)
*>-distrib-+ᶜ (Ψ ⊙ η) (γ ∙ p) (δ ∙ q) = begin
  (Ψ ⊙ η) *> ((γ ∙ p) +ᶜ (δ ∙ q))                 ≈⟨ +ᶜ-cong (·ᶜ-distribʳ-+ᶜ p q η) (*>-distrib-+ᶜ Ψ γ δ) ⟩
  (p ·ᶜ η +ᶜ q ·ᶜ η) +ᶜ Ψ *> γ +ᶜ Ψ *> δ          ≈⟨ +ᶜ-cong ≈ᶜ-refl (+ᶜ-comm (Ψ *> γ) (Ψ *> δ)) ⟩
  (p ·ᶜ η +ᶜ q ·ᶜ η) +ᶜ Ψ *> δ +ᶜ Ψ *> γ          ≈⟨ +ᶜ-assoc (p ·ᶜ η) (q ·ᶜ η) (Ψ *> δ +ᶜ Ψ *> γ) ⟩
  p ·ᶜ η +ᶜ q ·ᶜ η +ᶜ Ψ *> δ +ᶜ Ψ *> γ            ≈⟨ +ᶜ-comm (p ·ᶜ η) (q ·ᶜ η +ᶜ Ψ *> δ +ᶜ Ψ *> γ) ⟩
  (q ·ᶜ η +ᶜ Ψ *> δ +ᶜ Ψ *> γ) +ᶜ p ·ᶜ η          ≈⟨ +ᶜ-assoc _ _ _ ⟩
  q ·ᶜ η +ᶜ (Ψ *> δ +ᶜ Ψ *> γ) +ᶜ p ·ᶜ η          ≈⟨ +ᶜ-cong ≈ᶜ-refl (+ᶜ-assoc (Ψ *> δ) (Ψ *> γ) (p ·ᶜ η)) ⟩
  q ·ᶜ η +ᶜ Ψ *> δ +ᶜ Ψ *> γ +ᶜ p ·ᶜ η            ≈˘⟨ +ᶜ-assoc _ _ _ ⟩
  (q ·ᶜ η +ᶜ Ψ *> δ) +ᶜ Ψ *> γ +ᶜ p ·ᶜ η          ≈⟨ +ᶜ-cong ≈ᶜ-refl (+ᶜ-comm (Ψ *> γ) (p ·ᶜ η)) ⟩
  (q ·ᶜ η +ᶜ Ψ *> δ) +ᶜ p ·ᶜ η +ᶜ Ψ *> γ          ≈⟨ +ᶜ-comm _ _ ⟩
  ((p ·ᶜ η +ᶜ Ψ *> γ) +ᶜ q ·ᶜ η +ᶜ Ψ *> δ)        ∎
  where open import Tools.Reasoning.Equivalence ≈ᶜ-equivalence

-- Modality substitution application distributes over context scaling.
-- Ψ *> (pγ) ≡ p ·ᶜ (Ψ *> γ).
-- Proof by induction on Ψ using zero and associtivity of multiplication,
-- and distributivity of multiplication over addition.

*>-distrib-·ᶜ : (Ψ : Substₘ m n) (p : M) (γ : Conₘ n) → Ψ *> (p ·ᶜ γ) ≈ᶜ p ·ᶜ (Ψ *> γ)
*>-distrib-·ᶜ [] p ε = ≈ᶜ-sym (·ᶜ-zeroʳ p)
*>-distrib-·ᶜ (Ψ ⊙ δ) p (γ ∙ q) = begin
  (p · q) ·ᶜ δ +ᶜ Ψ *> (p ·ᶜ γ)  ≈⟨ +ᶜ-cong (·ᶜ-assoc p q δ) (*>-distrib-·ᶜ Ψ p γ) ⟩
  p ·ᶜ (q ·ᶜ δ) +ᶜ p ·ᶜ (Ψ *> γ) ≈˘⟨ ·ᶜ-distribˡ-+ᶜ p (q ·ᶜ δ) (Ψ *> γ) ⟩
  p ·ᶜ (q ·ᶜ δ +ᶜ Ψ *> γ)        ∎
  where open import Tools.Reasoning.Equivalence ≈ᶜ-equivalence

-- Modality substitution application is linear, i.e. distributes over addition and scaling
-- Ψ *> (pγ +ᶜ qδ) ≡ p ·ᶜ (Ψ *> γ) +ᶜ q ·ᶜ (Ψ *> δ)

-- Modality substitution application is linear, i.e. distributes over addition and scaling.
-- Ψ *> (pγ +ᶜ qδ) ≡ p ·ᶜ (Ψ *> γ) +ᶜ q ·ᶜ (Ψ *> δ).
-- Follows from the distributivity over addition and multiplication.

*>-linear : (Ψ : Substₘ m n) (p q : M) (γ δ : Conₘ n)
          → Ψ *> (p ·ᶜ γ +ᶜ q ·ᶜ δ) ≈ᶜ p ·ᶜ Ψ *> γ +ᶜ q ·ᶜ Ψ *> δ
*>-linear Ψ p q γ δ = begin
  Ψ *> (p ·ᶜ γ +ᶜ q ·ᶜ δ)        ≈⟨ *>-distrib-+ᶜ Ψ (p ·ᶜ γ) (q ·ᶜ δ) ⟩
  Ψ *> (p ·ᶜ γ) +ᶜ Ψ *> (q ·ᶜ δ) ≈⟨ +ᶜ-cong (*>-distrib-·ᶜ Ψ p γ) (*>-distrib-·ᶜ Ψ q δ) ⟩
  (p ·ᶜ Ψ *> γ +ᶜ q ·ᶜ Ψ *> δ)   ∎
  where open import Tools.Reasoning.Equivalence ≈ᶜ-equivalence

*>-sub-distrib-∧ᶜ : (Ψ : Substₘ m n) (γ δ : Conₘ n) → Ψ *> (γ ∧ᶜ δ) ≤ᶜ Ψ *> γ ∧ᶜ Ψ *> δ
*>-sub-distrib-∧ᶜ [] ε ε = ≤ᶜ-reflexive (≈ᶜ-sym (∧ᶜ-idem 𝟘ᶜ))
*>-sub-distrib-∧ᶜ (Ψ ⊙ η) (γ ∙ p) (δ ∙ q) = begin
  (Ψ ⊙ η) *> ((γ ∙ p) ∧ᶜ (δ ∙ q)) ≡⟨⟩
  (Ψ ⊙ η) *> (γ ∧ᶜ δ ∙ p ∧ q)     ≡⟨⟩
  (p ∧ q) ·ᶜ η +ᶜ Ψ *> (γ ∧ᶜ δ)
    ≤⟨ +ᶜ-monotoneʳ (*>-sub-distrib-∧ᶜ Ψ γ δ) ⟩
  (p ∧ q) ·ᶜ η +ᶜ (Ψγ ∧ᶜ Ψδ)
    ≈⟨ +ᶜ-cong (·ᶜ-distribʳ-∧ᶜ p q η) ≈ᶜ-refl ⟩
  (pη ∧ᶜ qη) +ᶜ (Ψγ ∧ᶜ Ψδ)
    ≈⟨ +ᶜ-distribʳ-∧ᶜ ((Ψ *> γ) ∧ᶜ (Ψ *> δ)) (p ·ᶜ η) (q ·ᶜ η) ⟩
  (pη +ᶜ (Ψγ ∧ᶜ Ψδ)) ∧ᶜ (qη +ᶜ (Ψγ ∧ᶜ Ψδ))
    ≈⟨ ∧ᶜ-cong (+ᶜ-distribˡ-∧ᶜ pη Ψγ Ψδ) (+ᶜ-distribˡ-∧ᶜ qη Ψγ Ψδ) ⟩
  ((pη +ᶜ Ψγ) ∧ᶜ (pη +ᶜ Ψδ)) ∧ᶜ ((qη +ᶜ Ψγ) ∧ᶜ (qη +ᶜ Ψδ))
    ≤⟨ ∧ᶜ-monotone (∧ᶜ-decreasingˡ (pη +ᶜ Ψγ) (pη +ᶜ Ψδ)) (∧ᶜ-decreasingʳ (qη +ᶜ Ψγ) (qη +ᶜ Ψδ)) ⟩
  (pη +ᶜ Ψγ) ∧ᶜ (qη +ᶜ Ψδ) ≡⟨⟩
  (Ψ ⊙ η) *> (γ ∙ p) ∧ᶜ (Ψ ⊙ η) *> (δ ∙ q) ∎
  where
  open import Tools.Reasoning.PartialOrder ≤ᶜ-poset
  Ψγ = Ψ *> γ
  Ψδ = Ψ *> δ
  pη = p ·ᶜ η
  qη = q ·ᶜ η

--- The zero-context is a right zero to modality substitution application.
-- Ψ *> 𝟘ᶜ ≡ 𝟘ᶜ.
-- Proof by induction on Ψ using zero of multiplication and identity of addition.

*>-zeroʳ : (Ψ : Substₘ m n) → Ψ *> 𝟘ᶜ ≈ᶜ 𝟘ᶜ
*>-zeroʳ []      = ≈ᶜ-refl
*>-zeroʳ (Ψ ⊙ γ) = begin
  (Ψ ⊙ γ) *> 𝟘ᶜ       ≡⟨⟩
  𝟘 ·ᶜ γ +ᶜ (Ψ *> 𝟘ᶜ) ≈⟨ +ᶜ-cong (·ᶜ-zeroˡ γ) (*>-zeroʳ Ψ) ⟩
  𝟘ᶜ +ᶜ 𝟘ᶜ            ≈⟨ +ᶜ-identityˡ 𝟘ᶜ ⟩
  𝟘ᶜ                  ∎
  where open import Tools.Reasoning.Equivalence ≈ᶜ-equivalence

-- Modality substitution application is a monotone function.
-- If γ ≤ᶜ δ, then Ψ *> γ ≤ᶜ Ψ *> δ.
-- Proof by induction on Ψ using monotonicity of addition and multiplication.

*>-monotone : {γ δ : Conₘ n} (Ψ : Substₘ m n) → γ ≤ᶜ δ → Ψ *> γ ≤ᶜ Ψ *> δ
*>-monotone {γ = ε}     {ε}      []      γ≤δ = ≤ᶜ-refl
*>-monotone {γ = γ ∙ p} {δ ∙ q} (Ψ ⊙ η) (γ≤δ ∙ p≤q) = +ᶜ-monotone (·ᶜ-monotoneˡ p≤q) (*>-monotone Ψ γ≤δ)

-- Matrix/vector multiplication is associative.
-- (Ψ <*> Φ) *> γ ≡ Ψ *> (Φ *> γ).
-- Proof by induction on γ using linearity of matrix multiplication.

<*>-*>-assoc : {ℓ m n : Nat} (Ψ : Substₘ m n) (Φ : Substₘ n ℓ) (γ : Conₘ ℓ)
             → (Ψ <*> Φ) *> γ ≈ᶜ Ψ *> (Φ *> γ)
<*>-*>-assoc Ψ [] ε = ≈ᶜ-sym (*>-zeroʳ Ψ)
<*>-*>-assoc Ψ (Φ ⊙ δ) (γ ∙ p) = begin
  p ·ᶜ (Ψ *> δ) +ᶜ (Ψ <*> Φ) *> γ ≈⟨ +ᶜ-cong (≈ᶜ-sym (*>-distrib-·ᶜ Ψ p δ)) (<*>-*>-assoc Ψ Φ γ) ⟩
  Ψ *> (p ·ᶜ δ) +ᶜ Ψ *> (Φ *> γ)  ≈˘⟨ *>-distrib-+ᶜ Ψ (p ·ᶜ δ) (Φ *> γ) ⟩
  Ψ *> (p ·ᶜ δ +ᶜ Φ *> γ)         ∎
  where open import Tools.Reasoning.Equivalence ≈ᶜ-equivalence

------------------------------------------
-- Properties of specific substitutions --
------------------------------------------

-- Application of a shifted substitution.
-- wk1Substₘ Ψ *> γ ≡ (Ψ *> γ) ∙ 𝟘.
-- Proof by induction on γ using identity of addition and zero of multiplication

wk1Substₘ-app : (Ψ : Substₘ m n) (γ : Conₘ n) → wk1Substₘ Ψ *> γ ≈ᶜ (Ψ *> γ) ∙ 𝟘
wk1Substₘ-app [] ε            = ≈ᶜ-refl
wk1Substₘ-app (Ψ ⊙ δ) (γ ∙ p) = begin
  wk1Substₘ (Ψ ⊙ δ) *> (γ ∙ p) ≡⟨⟩
  ((p ·ᶜ δ) ∙ (p · 𝟘)) +ᶜ wk1Substₘ Ψ *> γ ≈⟨ +ᶜ-cong (≈ᶜ-refl ∙ (proj₂ ·-zero p)) (wk1Substₘ-app Ψ γ) ⟩
  ((p ·ᶜ δ) ∙ 𝟘) +ᶜ ((Ψ *> γ) ∙ 𝟘) ≡⟨⟩
  (p ·ᶜ δ) +ᶜ (Ψ *> γ) ∙ (𝟘 + 𝟘) ≈⟨ ≈ᶜ-refl ∙ (proj₁ +-identity 𝟘) ⟩
  ((Ψ ⊙ δ) *> (γ ∙ p)) ∙ 𝟘 ∎
  where open import Tools.Reasoning.Equivalence ≈ᶜ-equivalence


-- Application of a lifted substitution.
-- liftSubstₘ Ψ *> (γ ∙ p) ≡ (Ψ *> γ) ∙ p.
-- Proof by induction on γ using lemma on application of a shifted substitution.

liftSubstₘ-app : (Ψ : Substₘ m n) (γ : Conₘ n) (p : M)
               → liftSubstₘ Ψ *> (γ ∙ p) ≈ᶜ (Ψ *> γ) ∙ p
liftSubstₘ-app [] ε p = begin -- cong₂ _∙_ (sym γ′) (sym p′)
  liftSubstₘ [] *> (ε ∙ p)    ≡⟨⟩
  ([] ⊙ (𝟘ᶜ ∙ 𝟙)) *> (ε ∙ p)  ≡⟨⟩
  p ·ᶜ (𝟘ᶜ ∙ 𝟙) +ᶜ 𝟘ᶜ         ≡⟨⟩
  ((p ·ᶜ 𝟘ᶜ) ∙ (p · 𝟙)) +ᶜ 𝟘ᶜ ≈⟨ +ᶜ-identityʳ _ ⟩
  (p ·ᶜ 𝟘ᶜ) ∙ (p · 𝟙)         ≈⟨ (·ᶜ-zeroʳ p) ∙ (proj₂ ·-identity p) ⟩
  𝟘ᶜ ∙ p                      ≡⟨⟩
  ([] *> ε) ∙ p ∎
  where open import Tools.Reasoning.Equivalence ≈ᶜ-equivalence

liftSubstₘ-app (Ψ ⊙ η) γ p = begin
  liftSubstₘ (Ψ ⊙ η) *> (γ ∙ p)             ≡⟨⟩
  (wk1Substₘ (Ψ ⊙ η) ⊙ (𝟘ᶜ ∙ 𝟙)) *> (γ ∙ p) ≡⟨⟩
  p ·ᶜ (𝟘ᶜ ∙ 𝟙) +ᶜ (wk1Substₘ (Ψ ⊙ η) *> γ)
     ≈⟨ +ᶜ-cong ((·ᶜ-zeroʳ p) ∙ (proj₂ ·-identity p)) (wk1Substₘ-app (Ψ ⊙ η) γ) ⟩
  (𝟘ᶜ ∙ p) +ᶜ (((Ψ ⊙ η) *> γ) ∙ 𝟘) ≈⟨ (+ᶜ-identityˡ ((Ψ ⊙ η) *> γ)) ∙ (proj₂ +-identity p) ⟩
  ((Ψ ⊙ η) *> γ) ∙ p ∎
  where open import Tools.Reasoning.Equivalence ≈ᶜ-equivalence

-- The identity matrix is a left identity to substitution application.
-- idSubstₘ *> γ ≡ γ.
-- Proof by identity of addition, multiplication and matrix multiplication,
-- zero of multiplication and lemma on the application of shifted substitution matrices.

*>-identityˡ : (γ : Conₘ n) → idSubstₘ *> γ ≈ᶜ γ
*>-identityˡ ε       = ≈ᶜ-refl
*>-identityˡ (γ ∙ p) = begin
  idSubstₘ *> (γ ∙ p) ≡⟨⟩
  ((p ·ᶜ 𝟘ᶜ) ∙ (p · 𝟙)) +ᶜ (wk1Substₘ idSubstₘ *> γ)
    ≈⟨ +ᶜ-cong ((·ᶜ-zeroʳ p) ∙ (proj₂ ·-identity p)) (wk1Substₘ-app idSubstₘ γ) ⟩
  ((𝟘ᶜ ∙ p) +ᶜ ((idSubstₘ *> γ) ∙ 𝟘))
    ≈⟨ (+ᶜ-identityˡ _) ∙ (proj₂ +-identity p) ⟩
  (idSubstₘ *> γ) ∙ p ≈⟨ (*>-identityˡ γ) ∙ ≈-refl ⟩
  γ ∙ p ∎
  where open import Tools.Reasoning.Equivalence ≈ᶜ-equivalence

-------------------------------
-- Well-formed substitutions --
-------------------------------

-- Substitting a single (well-used) variable is a well-formed substitution
-- If γ ▸ u, then sgSubstₘ γ ▶ sgSubst u
-- Proof by cases
-- Case x0 uses identity of addition, multiplication and matrix mutiplication.
-- Case x +1 uses identity of addition and matrix multiplication and zero of multiplicaiton.

wf-sgSubstₘ : γ ▸ u → sgSubstₘ γ ▶ sgSubst u
wf-sgSubstₘ {γ = γ} γ▸u x0 = sub γ▸u eq
  where
  open import Tools.Reasoning.PartialOrder ≤ᶜ-poset
  eq = begin
    𝟙 ·ᶜ γ +ᶜ idSubstₘ *> 𝟘ᶜ ≈⟨ +ᶜ-cong (·ᶜ-identityˡ γ) (*>-identityˡ 𝟘ᶜ) ⟩
    γ +ᶜ 𝟘ᶜ ≈⟨ +ᶜ-identityʳ γ ⟩
    γ ∎
wf-sgSubstₘ {γ = γ} γ▸u (x +1) = sub var eq
  where
  open import Tools.Reasoning.PartialOrder ≤ᶜ-poset
  eq = begin
    𝟘 ·ᶜ γ +ᶜ idSubstₘ *> (𝟘ᶜ , x ≔ 𝟙) ≈⟨ +ᶜ-cong (·ᶜ-zeroˡ γ) (*>-identityˡ _) ⟩
    𝟘ᶜ +ᶜ (𝟘ᶜ , x ≔ 𝟙)                 ≈⟨ +ᶜ-identityˡ _ ⟩
    𝟘ᶜ , x ≔ 𝟙                         ∎

-- Shifting a well-formed substitution is well-formed.
-- If Ψ ▶ σ, then wk1Substₘ Ψ ▶ wk1Subst σ.
-- Proof using lemmata on the application of a shifted substitution matrix
-- and shifted modality context.

wf-wk1Substₘ : (Ψ : Substₘ m n) (σ : Subst m n) → Ψ ▶ σ → wk1Substₘ Ψ ▶ wk1Subst σ
wf-wk1Substₘ Ψ σ Ψ▶σ x = sub (wk1-usage (Ψ▶σ x)) (≤ᶜ-reflexive (wk1Substₘ-app Ψ _))

-- Lifting a well-formed substitution is well-formed
-- If Ψ ▶ σ, then liftSubstₘ Ψ ▶ liftSubst σ
-- Proof by cases
-- Case x0 uses identity of addition and multiplication and zero of matrix multiplication.
-- Case x +1 uses identity of addition and zero of multiplication.

wf-liftSubstₘ : {Ψ : Substₘ m n} → Ψ ▶ σ → liftSubstₘ Ψ ▶ liftSubst σ
wf-liftSubstₘ {Ψ = Ψ} Ψ▶σ x0 = sub var eq
  where
  open import Tools.Reasoning.PartialOrder ≤ᶜ-poset
  eq = begin
    ((𝟙 ·ᶜ 𝟘ᶜ) ∙ (𝟙 · 𝟙)) +ᶜ wk1Substₘ Ψ *> 𝟘ᶜ
                    ≈⟨ +ᶜ-cong ((·ᶜ-zeroʳ 𝟙) ∙ (proj₁ ·-identity 𝟙)) (*>-zeroʳ (wk1Substₘ Ψ)) ⟩
    (𝟘ᶜ ∙ 𝟙) +ᶜ 𝟘ᶜ ≈⟨ +ᶜ-identityʳ _ ⟩
    𝟘ᶜ ∙ 𝟙         ≡⟨⟩
    𝟘ᶜ , x0 ≔ 𝟙    ∎

wf-liftSubstₘ {Ψ = Ψ} Ψ▶σ (x +1) = sub (wf-wk1Substₘ Ψ _ Ψ▶σ x) eq
  where
  open import Tools.Reasoning.PartialOrder ≤ᶜ-poset
  eq = begin
    (𝟘 ·ᶜ 𝟘ᶜ ∙ 𝟘 · 𝟙) +ᶜ wk1Substₘ Ψ *> (𝟘ᶜ , x ≔ 𝟙)
      ≈⟨ +ᶜ-cong ((·ᶜ-zeroʳ 𝟘) ∙ (proj₁ ·-zero 𝟙)) ≈ᶜ-refl ⟩
    𝟘ᶜ +ᶜ wk1Substₘ Ψ *> (𝟘ᶜ , x ≔ 𝟙)
      ≈⟨ +ᶜ-identityˡ _ ⟩
    wk1Substₘ Ψ *> (𝟘ᶜ , x ≔ 𝟙) ∎

-- Extending a well-formed substitution with a well-used term gives a well-formed substitution.
-- If Ψ ▶ σ and γ ▸ t, then (Ψ ∙ γ) ▶ consSubst σ t.
-- Proof by cases.
-- Case x0 uses identity of addition, multiplication and zero of matrix multiplication
-- Case x +1 uses identity of addition and zero of multiplication

wf-consSubstₘ : {Ψ : Substₘ m n} {γ : Conₘ m} → Ψ ▶ σ → γ ▸ t → Ψ ⊙ γ ▶ consSubst σ t
wf-consSubstₘ {Ψ = Ψ} {γ = γ} Ψ▶σ γ▸t x0 = sub γ▸t eq
  where
  open import Tools.Reasoning.PartialOrder ≤ᶜ-poset
  eq = begin
       𝟙 ·ᶜ γ +ᶜ Ψ *> 𝟘ᶜ ≈⟨ +ᶜ-cong (·ᶜ-identityˡ γ) (*>-zeroʳ Ψ) ⟩
       γ +ᶜ 𝟘ᶜ           ≈⟨ +ᶜ-identityʳ _ ⟩
       γ                 ∎
wf-consSubstₘ {Ψ = Ψ} {γ = γ} Ψ▶σ γ▸t (x +1) = sub (Ψ▶σ x) eq
  where
  open import Tools.Reasoning.PartialOrder ≤ᶜ-poset
  eq = begin
         𝟘 ·ᶜ γ +ᶜ Ψ *> (𝟘ᶜ , x ≔ 𝟙) ≈⟨ +ᶜ-cong (·ᶜ-zeroˡ _) ≈ᶜ-refl ⟩
         𝟘ᶜ +ᶜ Ψ *> (𝟘ᶜ , x ≔ 𝟙)     ≈⟨ +ᶜ-identityˡ _ ⟩
         Ψ *> (𝟘ᶜ , x ≔ 𝟙)           ∎

---------------------------------------
-- Substitution lemma for modalities --
---------------------------------------

-- Substitution lemma.
-- If Ψ ▶ σ and γ ▸ t, then Ψ *> γ ▸ t[σ].
-- Proof by induction on γ ▸ t using linearity of matrix multiplication
-- and well-formedness of lifted substitution matrices.

substₘ-lemma : (Ψ : Substₘ m n) (σ : Subst m n) → Ψ ▶ σ → γ ▸ t → substₘ Ψ γ ▸ U.subst σ t
substₘ-lemma Ψ σ Ψ▶σ Uₘ     = sub Uₘ (≤ᶜ-reflexive (*>-zeroʳ Ψ))
substₘ-lemma Ψ σ Ψ▶σ ℕₘ     = sub ℕₘ (≤ᶜ-reflexive (*>-zeroʳ Ψ))
substₘ-lemma Ψ σ Ψ▶σ Emptyₘ = sub Emptyₘ (≤ᶜ-reflexive (*>-zeroʳ Ψ))
substₘ-lemma Ψ σ Ψ▶σ Unitₘ  = sub Unitₘ (≤ᶜ-reflexive (*>-zeroʳ Ψ))

substₘ-lemma Ψ σ Ψ▶σ (Πₘ γ▸F δ▸G) = sub (Πₘ γ▸F′ δ▸G″) (≤ᶜ-reflexive (*>-distrib-+ᶜ Ψ _ _))
  where
  γ▸F′ = substₘ-lemma Ψ σ Ψ▶σ γ▸F
  δ▸G′ = substₘ-lemma (liftSubstₘ Ψ) (liftSubst σ) (wf-liftSubstₘ Ψ▶σ) δ▸G
  δ▸G″ = sub δ▸G′ (≤ᶜ-reflexive (≈ᶜ-sym (liftSubstₘ-app Ψ _ _)))

substₘ-lemma Ψ σ Ψ▶σ (Σₘ γ▸F δ▸G) = sub (Σₘ γ▸F′ δ▸G″) (≤ᶜ-reflexive (*>-distrib-+ᶜ Ψ _ _))
  where
  γ▸F′ = substₘ-lemma Ψ σ Ψ▶σ γ▸F
  δ▸G′ = substₘ-lemma (liftSubstₘ Ψ) (liftSubst σ) (wf-liftSubstₘ Ψ▶σ) δ▸G
  δ▸G″ = sub δ▸G′ (≤ᶜ-reflexive (≈ᶜ-sym (liftSubstₘ-app Ψ _ _)))

substₘ-lemma Ψ σ Ψ▶σ (var {x}) = Ψ▶σ x

substₘ-lemma Ψ σ Ψ▶σ (lamₘ γ▸t) = lamₘ (sub γ▸t′ (≤ᶜ-reflexive (≈ᶜ-sym (liftSubstₘ-app Ψ _ _))))
  where
  γ▸t′ = (substₘ-lemma (liftSubstₘ Ψ) (liftSubst σ) (wf-liftSubstₘ Ψ▶σ) γ▸t)

substₘ-lemma Ψ σ Ψ▶σ (_∘ₘ_ {γ} {δ = δ} {p = p} γ▸t δ▸u) = sub
  ((substₘ-lemma Ψ σ Ψ▶σ γ▸t) ∘ₘ (substₘ-lemma Ψ σ Ψ▶σ δ▸u))
  eq
  where
  open import Tools.Reasoning.PartialOrder ≤ᶜ-poset
  eq = begin
    Ψ *> (γ +ᶜ p ·ᶜ δ)      ≈⟨ *>-distrib-+ᶜ Ψ γ (p ·ᶜ δ) ⟩
    Ψ *> γ +ᶜ Ψ *> (p ·ᶜ δ) ≈⟨ +ᶜ-cong ≈ᶜ-refl (*>-distrib-·ᶜ Ψ p δ) ⟩
    Ψ *> γ +ᶜ p ·ᶜ (Ψ *> δ) ∎

substₘ-lemma Ψ σ Ψ▶σ (prodₘ {γ = γ} {δ = δ} γ▸t δ▸u PE.refl) = sub
  (prodₘ! (substₘ-lemma Ψ σ Ψ▶σ γ▸t) (substₘ-lemma Ψ σ Ψ▶σ δ▸u))
  (≤ᶜ-reflexive (*>-distrib-+ᶜ Ψ γ δ))

substₘ-lemma Ψ σ Ψ▶σ (fstₘ γ▸t) = sub
  (fstₘ (sub (substₘ-lemma Ψ σ Ψ▶σ γ▸t) (≤ᶜ-reflexive (≈ᶜ-sym (*>-zeroʳ Ψ)))))
  (≤ᶜ-reflexive (*>-zeroʳ Ψ))

substₘ-lemma Ψ σ Ψ▶σ (sndₘ γ▸t) = sub
  (sndₘ (sub (substₘ-lemma Ψ σ Ψ▶σ γ▸t) (≤ᶜ-reflexive (≈ᶜ-sym (*>-zeroʳ Ψ)))))
  (≤ᶜ-reflexive (*>-zeroʳ Ψ))




substₘ-lemma Ψ σ Ψ▶σ (prodrecₘ {γ = γ} {δ = δ} {p} γ▸t δ▸u) = sub
  (prodrecₘ γ▸t′ (sub δ▸u′ eq))
  eq′
  where
  γ▸t′ = substₘ-lemma Ψ σ Ψ▶σ γ▸t
  δ▸u′ = substₘ-lemma (liftSubstₘ (liftSubstₘ Ψ)) (liftSubst (liftSubst σ))
                      (wf-liftSubstₘ (wf-liftSubstₘ Ψ▶σ)) δ▸u
  import Tools.Reasoning.PartialOrder ≤ᶜ-poset as R₁
  eq = R₁.begin
    Ψ *> δ ∙ p ∙ p
      R₁.≈⟨ (≈ᶜ-sym (liftSubstₘ-app Ψ δ p)) ∙ ≈-refl ⟩
    (wk1Substₘ Ψ ⊙ (𝟘ᶜ ∙ 𝟙)) *> (δ ∙ p) ∙ p
      R₁.≈⟨ ≈ᶜ-sym (liftSubstₘ-app (wk1Substₘ Ψ ⊙ (𝟘ᶜ ∙ 𝟙)) (δ ∙ p) p) ⟩
    ((wk1Substₘ (wk1Substₘ Ψ) ⊙ (𝟘ᶜ ∙ 𝟙 ∙ 𝟘) ⊙ (𝟘ᶜ ∙ 𝟙)) *> (δ ∙ p ∙ p))
      R₁.≡⟨⟩
    p ·ᶜ (𝟘ᶜ ∙ 𝟘 ∙ 𝟙) +ᶜ p ·ᶜ (𝟘ᶜ ∙ 𝟙 ∙ 𝟘) +ᶜ ((wk1Substₘ (wk1Substₘ Ψ)) *> δ)
      R₁.≡⟨⟩
    (p ·ᶜ 𝟘ᶜ ∙ p · 𝟘 ∙ p · 𝟙) +ᶜ (p ·ᶜ 𝟘ᶜ ∙ p · 𝟙 ∙ p · 𝟘) +ᶜ ((wk1Substₘ (wk1Substₘ Ψ)) *> δ) R₁.∎
  import Tools.Reasoning.PartialOrder ≤ᶜ-poset as R₂
  eq′ = R₂.begin
    Ψ *> (p ·ᶜ γ +ᶜ δ)      R₂.≈⟨ *>-distrib-+ᶜ Ψ (p ·ᶜ γ) δ ⟩
    Ψ *> (p ·ᶜ γ) +ᶜ Ψ *> δ R₂.≈⟨ +ᶜ-cong (*>-distrib-·ᶜ Ψ p γ) ≈ᶜ-refl ⟩
    p ·ᶜ Ψ *> γ +ᶜ Ψ *> δ   R₂.∎

substₘ-lemma Ψ σ Ψ▶σ zeroₘ = sub zeroₘ (≤ᶜ-reflexive (*>-zeroʳ Ψ))

substₘ-lemma Ψ σ Ψ▶σ (sucₘ γ▸t) = sucₘ (substₘ-lemma Ψ σ Ψ▶σ γ▸t)

  -- subst₂ _▸_ {!!} refl (natrecₘ γ▸z′ δ▸s″ η▸n′ {!δ′≡!})
  -- subst₂ _▸_ eq refl (natrecₘ γ▸z′ γ▸s″ δ▸n′)
substₘ-lemma Ψ σ Ψ▶σ (natrecₘ {δ = δ} {p} {r} γ▸z δ▸s η▸n) = subst₂ _▸_ refl refl (sub (natrecₘ γ▸z′ δ▸s″ η▸n′) {!!})
  where
  γ▸z′ = substₘ-lemma Ψ σ Ψ▶σ γ▸z
  δ▸s′ = substₘ-lemma (liftSubstₘ (liftSubstₘ Ψ)) (liftSubst (liftSubst σ)) (wf-liftSubstₘ (wf-liftSubstₘ Ψ▶σ)) δ▸s
  η▸n′ = substₘ-lemma Ψ σ Ψ▶σ η▸n
  eq′ = {!!}
  -- begin
  --     liftSubstₘ (liftSubstₘ Ψ) *> (δ ∙ p ∙ r)
  --       ≡⟨ liftSubstₘ-app (liftSubstₘ Ψ) (δ ∙ p) r ⟩
  --     ((p ·ᶜ 𝟘ᶜ) ∙ (Modality._·_ 𝕄 p (Modality.𝟙 𝕄)) +ᶜ wk1Substₘ Ψ *> δ) ∙ r
  --       ≡⟨ cong (_∙ r) (cong₂ _+ᶜ_ (cong₂ _∙_ (·ᶜ-zeroʳ p)
  --                      (proj₂ (Modality.·-Identity 𝕄) p)) (wk1Substₘ-app Ψ δ)) ⟩
  --     (𝟘ᶜ +ᶜ Ψ *> δ) ∙ (Modality._+_ 𝕄 p (Modality.𝟘 𝕄)) ∙ r
  --       ≡⟨ cong (_∙ r) (cong₂ _∙_ (+ᶜ-identityˡ (Ψ *> δ))
  --                      (proj₂ (Modality.+-Identity 𝕄) p)) ⟩
  --     (Ψ *> δ) ∙ p ∙ r ∎
  δ▸s″ = subst₂ _▸_ eq′ refl δ▸s′
  -- eq = begin
  --    (𝕄 Modality.*) r ·ᶜ (substₘ Ψ γ +ᶜ p ·ᶜ substₘ Ψ δ)
  --      ≡⟨ cong₂ _·ᶜ_ refl (cong₂ _+ᶜ_ refl (sym (*>-distrib-·ᶜ Ψ p δ))) ⟩
  --    _ ≡⟨ cong₂ _·ᶜ_ refl (sym (*>-distrib-+ᶜ Ψ γ (p ·ᶜ δ))) ⟩
  --    _ ≡⟨ sym (*>-distrib-·ᶜ Ψ _ _) ⟩
  --    Ψ *> ((Modality._* 𝕄 r) ·ᶜ (γ +ᶜ p ·ᶜ δ)) ∎

substₘ-lemma Ψ σ Ψ▶σ (Emptyrecₘ γ▸t) = Emptyrecₘ (substₘ-lemma Ψ σ Ψ▶σ γ▸t)
substₘ-lemma Ψ σ Ψ▶σ starₘ           = sub starₘ (≤ᶜ-reflexive (*>-zeroʳ Ψ))
substₘ-lemma Ψ σ Ψ▶σ (sub γ▸t x)     = sub (substₘ-lemma Ψ σ Ψ▶σ γ▸t) (*>-monotone Ψ x)


-- Special case of substitution lemma for single substitutions.
-- If γ ∙ p ▸ t and δ ▸ u, then (γ +ᶜ pδ) ▸ t[u].
-- Follows from the substitution lemma.

sgSubstₘ-lemma : γ ∙ p ▸ t → δ ▸ u → (γ +ᶜ p ·ᶜ δ) ▸ t [ u ]
sgSubstₘ-lemma {γ = γ} {p} {δ = δ} γ▸t δ▸u = {!!}
-- subst₂ _▸_ eq refl
--   (substₘ-lemma (sgSubstₘ _) (sgSubst _) (wf-sgSubstₘ δ▸u) γ▸t)
 -- where
  -- open import Tools.Reasoning
  -- eq = begin
  --   (idSubstₘ ∙ δ) *> (γ ∙ p) ≡⟨ +ᶜ-comm _ _ ⟩
  --   idSubstₘ *> γ +ᶜ p ·ᶜ δ   ≡⟨ cong₂ _+ᶜ_ (*>-identityˡ γ) refl ⟩
  --   γ +ᶜ p ·ᶜ δ               ∎

-- Special case of substitution lemma for double substitutions.
-- If γ ∙ q ∙ p ▸ t and δ ▸ u and η ▸ u′, then (γ +ᶜ pδ +ᶜ qη) ▸ t[u][u′].
-- Follows from the substitution lemma.

doubleSubstₘ-lemma : γ ∙ q ∙ p ▸ t → δ ▸ u → η ▸ u′ → (γ +ᶜ p ·ᶜ δ +ᶜ q ·ᶜ η) ▸ t [ u ][ u′ ]
doubleSubstₘ-lemma {γ = γ} {q} {p} {δ = δ} {η = η} γ▸t δ▸u η▸u′ = {!!}
-- subst₂ _▸_ eq refl
--   (substₘ-lemma (consSubstₘ (sgSubstₘ _) _) _
--                 (wf-consSubstₘ (wf-sgSubstₘ η▸u′) δ▸u) γ▸t)
--   where
--   eq = begin
--     p ·ᶜ δ +ᶜ q ·ᶜ η +ᶜ idSubstₘ *> γ ≡⟨ cong₂ _+ᶜ_ refl (cong₂ _+ᶜ_ refl (*>-identityˡ γ)) ⟩
--     p ·ᶜ δ +ᶜ q ·ᶜ η +ᶜ γ             ≡⟨ sym (+ᶜ-assoc (p ·ᶜ δ) (q ·ᶜ η) γ) ⟩
--     (p ·ᶜ δ +ᶜ q ·ᶜ η) +ᶜ γ           ≡⟨ +ᶜ-comm (p ·ᶜ δ +ᶜ q ·ᶜ η) γ ⟩
--     γ +ᶜ p ·ᶜ δ +ᶜ q ·ᶜ η             ∎

-------------------------------------
-- Substitution matrix calculation --
-------------------------------------

-- Column i of a calculated matrix is the calculated context of σ xᵢ.
-- ∥ σ ∥ *> 𝕖ᵢ ≡ ⌈ σ xᵢ ⌉.
-- Proof by induction on (the width of) substitution matrices.

substₘ-calc-col : (σ : Subst m n) (x : Fin n)
                → ∥ σ ∥ *> (𝟘ᶜ , x ≔ 𝟙) ≡ ⌈ σ x ⌉
substₘ-calc-col σ x0 = {!!}
-- begin
--    Modality.𝟙 𝕄 ·ᶜ ⌈ σ x0 ⌉ +ᶜ ∥ (λ x → σ (x +1)) ∥ *> 𝟘ᶜ
--      ≡⟨ cong₂ _+ᶜ_ (·ᶜ-identityˡ ⌈ σ x0 ⌉) (*>-zeroʳ  ∥ (λ x → σ (x +1)) ∥) ⟩
--    ⌈ σ x0 ⌉ +ᶜ 𝟘ᶜ
--      ≡⟨ +ᶜ-identityʳ ⌈ σ x0 ⌉ ⟩
--    ⌈ σ x0 ⌉ ∎
substₘ-calc-col σ (x +1) = {!!}
-- begin
--   Modality.𝟘 𝕄 ·ᶜ ⌈ σ x0 ⌉ +ᶜ ∥ (λ x₁ → σ (x₁ +1)) ∥ *> (𝟘ᶜ , x ≔ Modality.𝟙 𝕄)
--     ≡⟨ cong₂ _+ᶜ_ (·ᶜ-zeroˡ ⌈ σ x0 ⌉) (substₘ-calc-col (λ x₁ → σ (x₁ +1)) x) ⟩
--   𝟘ᶜ +ᶜ ⌈ σ (x +1) ⌉
--     ≡⟨ +ᶜ-identityˡ ⌈ σ (x +1) ⌉ ⟩
--   ⌈ σ (x +1) ⌉ ∎

-- A calculated substitution matrix is well-formed if all substituted terms are well-typed and well-used.
-- If ∀ x. (Γ ⊢ σ x ∷ A and γ ▸ σ x) then ∥ σ ∥ ▶ σ.
-- Proof by the corresponding property for modality contexts applied to each column.

substₘ-calc-correct : {Γ : Con Term m} {γ : Conₘ m} {A : Term m}
                    → (σ : Subst m n) → (∀ x → Γ ⊢ σ x ∷ A × γ ▸ σ x) → ∥ σ ∥ ▶ σ
substₘ-calc-correct σ well-typed x = subst₂ _▸_ (sym (substₘ-calc-col σ x)) refl
  (usage-calc-term′ (proj₁ (well-typed x)) (proj₂ (well-typed x)))

-- Each column of a calculated substitution matrix is an upper bound on valid contexts.
-- If γ ▸ σ xᵢ then γ ≤ᶜ ∥ σ ∥ *> 𝕖ᵢ.
-- Proof using the corresponding property for modality contexts applied to each column.

substₘ-calc-upper-bound : {γ : Conₘ m} → (σ : Subst m n) → (x : Fin n)
                        → γ ▸ σ x → γ ≤ᶜ ∥ σ ∥ *> (𝟘ᶜ , x ≔ 𝟙)
substₘ-calc-upper-bound σ x γ▸σx = subst₂ _≤ᶜ_ refl (sym (substₘ-calc-col σ x)) (usage-upper-bound γ▸σx)

--------------------------------------------------
-- Well-formedness of substitution compositions --
--------------------------------------------------

-- Composition of well-formed substitutions are well-formed.
-- If Ψ ▶ σ and Φ ▶ σ′ then (Ψ <*> Φ) ▶ (σ ₛ•ₛ σ′).
-- Proof using the substitution lemma and associtivity of matrix/vector pultiplication.

wf-compSubst : {Ψ : Substₘ m ℓ} {Φ : Substₘ ℓ n} {σ : Subst m ℓ} {σ′ : Subst ℓ n}
             → Ψ ▶ σ → Φ ▶ σ′ → (Ψ <*> Φ) ▶ (σ ₛ•ₛ σ′)
wf-compSubst {Ψ = Ψ} {Φ = Φ} {σ = σ} {σ′ = σ′} Ψ▶σ Φ▶σ′ x = {!!}
-- subst₂ _▸_
--   (sym (<*>-*>-assoc Ψ Φ (𝟘ᶜ , x ≔ 𝟙)))
--   refl
--   (substₘ-lemma Ψ σ Ψ▶σ (Φ▶σ′ x))
