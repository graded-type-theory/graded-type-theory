open import Definition.Modality

module Definition.Modality.Substitution.Properties
  {a} {M : Set a} (𝕄 : Modality M) where

open Modality 𝕄

open import Definition.Modality.Context 𝕄
open import Definition.Modality.Context.Properties 𝕄
open import Definition.Modality.Properties 𝕄
open import Definition.Modality.Substitution 𝕄
open import Definition.Modality.Usage 𝕄
open import Definition.Modality.Usage.Properties 𝕄
open import Definition.Modality.Usage.Weakening 𝕄
open import Definition.Mode 𝕄
open import Definition.Typed M using (_⊢_∷_; _⊢ˢ_∷_; _,_)
open import Definition.Untyped M as U renaming (_[_,_] to _[_,,_])

open import Tools.Bool using (T)
open import Tools.Fin
open import Tools.Function
open import Tools.Nat hiding (_+_)
open import Tools.Nullary
open import Tools.Product
open import Tools.PropositionalEquality as PE
import Tools.Reasoning.Equivalence
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
import Tools.Relation
open import Tools.Sum using (_⊎_; inj₁; inj₂)

private
  variable
    ℓ m n : Nat
    x y : Fin n
    γ γ′ δ η : Conₘ n
    t u u′ : Term n
    σ : Subst m n
    p q r : M
    mo : Mode
    mos mos₁ mos₂ : Mode-vector n

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
  (Ψ ⊙ η) *> ((γ ∙ p) +ᶜ (δ ∙ q))
    ≈⟨ +ᶜ-cong (·ᶜ-distribʳ-+ᶜ p q η) (*>-distrib-+ᶜ Ψ γ δ) ⟩
  (p ·ᶜ η +ᶜ q ·ᶜ η) +ᶜ Ψ *> γ +ᶜ Ψ *> δ
    ≈⟨ +ᶜ-congˡ (+ᶜ-comm (Ψ *> γ) (Ψ *> δ)) ⟩
  (p ·ᶜ η +ᶜ q ·ᶜ η) +ᶜ Ψ *> δ +ᶜ Ψ *> γ
    ≈⟨ +ᶜ-assoc (p ·ᶜ η) (q ·ᶜ η) (Ψ *> δ +ᶜ Ψ *> γ) ⟩
  p ·ᶜ η +ᶜ q ·ᶜ η +ᶜ Ψ *> δ +ᶜ Ψ *> γ
    ≈⟨ +ᶜ-comm (p ·ᶜ η) (q ·ᶜ η +ᶜ Ψ *> δ +ᶜ Ψ *> γ) ⟩
  (q ·ᶜ η +ᶜ Ψ *> δ +ᶜ Ψ *> γ) +ᶜ p ·ᶜ η
    ≈⟨ +ᶜ-assoc _ _ _ ⟩
  q ·ᶜ η +ᶜ (Ψ *> δ +ᶜ Ψ *> γ) +ᶜ p ·ᶜ η
    ≈⟨ +ᶜ-congˡ (+ᶜ-assoc (Ψ *> δ) (Ψ *> γ) (p ·ᶜ η)) ⟩
  q ·ᶜ η +ᶜ Ψ *> δ +ᶜ Ψ *> γ +ᶜ p ·ᶜ η
    ≈˘⟨ +ᶜ-assoc _ _ _ ⟩
  (q ·ᶜ η +ᶜ Ψ *> δ) +ᶜ Ψ *> γ +ᶜ p ·ᶜ η
    ≈⟨ +ᶜ-congˡ (+ᶜ-comm (Ψ *> γ) (p ·ᶜ η)) ⟩
  (q ·ᶜ η +ᶜ Ψ *> δ) +ᶜ p ·ᶜ η +ᶜ Ψ *> γ
    ≈⟨ +ᶜ-comm _ _ ⟩
  ((p ·ᶜ η +ᶜ Ψ *> γ) +ᶜ q ·ᶜ η +ᶜ Ψ *> δ) ∎
  where open Tools.Reasoning.Equivalence Conₘ-setoid

-- Modality substitution application distributes over context scaling.
-- Ψ *> (pγ) ≡ p ·ᶜ (Ψ *> γ).
-- Proof by induction on Ψ using zero and associtivity of multiplication,
-- and distributivity of multiplication over addition.

*>-distrib-·ᶜ : (Ψ : Substₘ m n) (p : M) (γ : Conₘ n)
              → Ψ *> (p ·ᶜ γ) ≈ᶜ p ·ᶜ (Ψ *> γ)
*>-distrib-·ᶜ [] p ε = ≈ᶜ-sym (·ᶜ-zeroʳ p)
*>-distrib-·ᶜ (Ψ ⊙ δ) p (γ ∙ q) = begin
  (p · q) ·ᶜ δ +ᶜ Ψ *> (p ·ᶜ γ)  ≈⟨ +ᶜ-cong (·ᶜ-assoc p q δ) (*>-distrib-·ᶜ Ψ p γ) ⟩
  p ·ᶜ (q ·ᶜ δ) +ᶜ p ·ᶜ (Ψ *> γ) ≈˘⟨ ·ᶜ-distribˡ-+ᶜ p (q ·ᶜ δ) (Ψ *> γ) ⟩
  p ·ᶜ (q ·ᶜ δ +ᶜ Ψ *> γ)        ∎
  where open Tools.Reasoning.Equivalence Conₘ-setoid

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
  where open Tools.Reasoning.Equivalence Conₘ-setoid

*>-sub-distrib-∧ᶜ : (Ψ : Substₘ m n) (γ δ : Conₘ n) → Ψ *> (γ ∧ᶜ δ) ≤ᶜ Ψ *> γ ∧ᶜ Ψ *> δ
*>-sub-distrib-∧ᶜ [] ε ε = begin
  𝟘ᶜ        ≈˘⟨ ∧ᶜ-idem _ ⟩
  𝟘ᶜ ∧ᶜ 𝟘ᶜ  ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
*>-sub-distrib-∧ᶜ (Ψ ⊙ η) (γ ∙ p) (δ ∙ q) = begin
  (p ∧ q) ·ᶜ η +ᶜ Ψ *> (γ ∧ᶜ δ)             ≤⟨ +ᶜ-monotone (≤ᶜ-reflexive (·ᶜ-distribʳ-∧ᶜ _ _ _)) (*>-sub-distrib-∧ᶜ Ψ _ _) ⟩
  (p ·ᶜ η ∧ᶜ q ·ᶜ η) +ᶜ (Ψ *> γ ∧ᶜ Ψ *> δ)  ≤⟨ +ᶜ-sub-interchangeable-∧ᶜ _ _ _ _ ⟩
  (p ·ᶜ η +ᶜ Ψ *> γ) ∧ᶜ q ·ᶜ η +ᶜ Ψ *> δ    ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- Modality substitution application sub-distributes over the two first arguments of ⊛ᶜ
-- Ψ *> γ ⊛ᶜ δ ▷ r ≤ (Ψ *> γ) ⊛ (Ψ *> δ) ▷ r
-- Proof by induction on Ψ using sub-distributivity and interchange properties of ⊛ᶜ

*>-sub-distrib-⊛ᶜ : (Ψ : Substₘ m n) (γ δ : Conₘ n) (r : M)
                   → Ψ *> (γ ⊛ᶜ δ ▷ r) ≤ᶜ (Ψ *> γ) ⊛ᶜ (Ψ *> δ) ▷ r
*>-sub-distrib-⊛ᶜ [] ε ε r = ≤ᶜ-reflexive (≈ᶜ-sym (⊛ᶜ-idem-𝟘ᶜ r))
*>-sub-distrib-⊛ᶜ (Ψ ⊙ η) (γ ∙ p) (δ ∙ q) r = begin
  (Ψ ⊙ η) *> ((γ ∙ p) ⊛ᶜ (δ ∙ q) ▷ r)
      ≡⟨⟩
  (Ψ ⊙ η) *> (γ ⊛ᶜ δ ▷ r ∙ p ⊛ q ▷ r)
      ≡⟨⟩
  p ⊛ q ▷ r ·ᶜ η +ᶜ Ψ *> (γ ⊛ᶜ δ ▷ r)
      ≤⟨ +ᶜ-monotone (·ᶜ-sub-distribʳ-⊛ p q r η) (*>-sub-distrib-⊛ᶜ Ψ γ δ r) ⟩
  (p ·ᶜ η) ⊛ᶜ (q ·ᶜ η) ▷ r +ᶜ (Ψ *> γ) ⊛ᶜ (Ψ *> δ) ▷ r
      ≤⟨ +ᶜ-sub-interchangable-⊛ᶜ r (p ·ᶜ η) (q ·ᶜ η) (Ψ *> γ) (Ψ *> δ) ⟩
  (p ·ᶜ η +ᶜ Ψ *> γ) ⊛ᶜ (q ·ᶜ η +ᶜ Ψ *> δ) ▷ r
      ≡⟨⟩
  ((Ψ ⊙ η) *> (γ ∙ p)) ⊛ᶜ ((Ψ ⊙ η) *> (δ ∙ q)) ▷ r ∎
  where open Tools.Reasoning.PartialOrder ≤ᶜ-poset

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
  where open Tools.Reasoning.Equivalence Conₘ-setoid

-- Modality substitution application is a monotone function.
-- If γ ≤ᶜ δ, then Ψ *> γ ≤ᶜ Ψ *> δ.
-- Proof by induction on Ψ using monotonicity of addition and multiplication.

*>-monotone : {γ δ : Conₘ n} (Ψ : Substₘ m n) → γ ≤ᶜ δ → Ψ *> γ ≤ᶜ Ψ *> δ
*>-monotone {γ = ε} {ε} [] γ≤δ = ≤ᶜ-refl
*>-monotone {γ = γ ∙ p} {δ ∙ q} (Ψ ⊙ η) (γ≤δ ∙ p≤q) =
  +ᶜ-monotone (·ᶜ-monotoneˡ p≤q) (*>-monotone Ψ γ≤δ)

-- The function Ψ *>_ preserves equivalence.

*>-cong : (Ψ : Substₘ m n) → γ ≈ᶜ δ → Ψ *> γ ≈ᶜ Ψ *> δ
*>-cong Ψ γ≈δ = ≤ᶜ-antisym
  (*>-monotone Ψ (≤ᶜ-reflexive γ≈δ))
  (*>-monotone Ψ (≤ᶜ-reflexive (≈ᶜ-sym γ≈δ)))

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
  where open Tools.Reasoning.Equivalence Conₘ-setoid

-- A corollary.

·ᶜ-*>-𝟘ᶜ,≔𝟙 :
  (Ψ : Substₘ m n) →
  p ·ᶜ Ψ *> (𝟘ᶜ , x ≔ 𝟙) ≈ᶜ Ψ *> (𝟘ᶜ , x ≔ p)
·ᶜ-*>-𝟘ᶜ,≔𝟙 {p = p} {x = x} Ψ = begin
  p ·ᶜ Ψ *> (𝟘ᶜ , x ≔ 𝟙)      ≈˘⟨ *>-distrib-·ᶜ Ψ _ _ ⟩
  Ψ *> (p ·ᶜ (𝟘ᶜ , x ≔ 𝟙))    ≡˘⟨ cong (Ψ *>_) (update-distrib-·ᶜ _ _ _ _) ⟩
  Ψ *> (p ·ᶜ 𝟘ᶜ , x ≔ p · 𝟙)  ≈⟨ *>-cong Ψ (update-cong (·ᶜ-zeroʳ _) (·-identityʳ _)) ⟩
  Ψ *> (𝟘ᶜ , x ≔ p)           ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid

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
  ((p ·ᶜ δ) ∙ (p · 𝟘)) +ᶜ wk1Substₘ Ψ *> γ
      ≈⟨ +ᶜ-cong (≈ᶜ-refl ∙ (·-zeroʳ p)) (wk1Substₘ-app Ψ γ) ⟩
  ((p ·ᶜ δ) ∙ 𝟘) +ᶜ ((Ψ *> γ) ∙ 𝟘)
      ≡⟨⟩
  (p ·ᶜ δ) +ᶜ (Ψ *> γ) ∙ (𝟘 + 𝟘)
     ≈⟨ ≈ᶜ-refl ∙ (+-identityˡ 𝟘) ⟩
  ((Ψ ⊙ δ) *> (γ ∙ p)) ∙ 𝟘         ∎
  where open Tools.Reasoning.Equivalence Conₘ-setoid


-- Application of a lifted substitution.
-- liftSubstₘ Ψ *> (γ ∙ p) ≡ (Ψ *> γ) ∙ p.
-- Proof by induction on γ using lemma on application of a shifted substitution.

liftSubstₘ-app : (Ψ : Substₘ m n) (γ : Conₘ n) (p : M)
               → liftSubstₘ Ψ *> (γ ∙ p) ≈ᶜ (Ψ *> γ) ∙ p
liftSubstₘ-app [] ε p = begin
  liftSubstₘ [] *> (ε ∙ p)   ≡⟨⟩
  ([] ⊙ (𝟘ᶜ ∙ 𝟙)) *> (ε ∙ p) ≡⟨⟩
  p ·ᶜ (𝟘ᶜ ∙ 𝟙) +ᶜ 𝟘ᶜ         ≡⟨⟩
  ((p ·ᶜ 𝟘ᶜ) ∙ (p · 𝟙)) +ᶜ 𝟘ᶜ ≈⟨ +ᶜ-identityʳ _ ⟩
  (p ·ᶜ 𝟘ᶜ) ∙ (p · 𝟙)        ≈⟨ (·ᶜ-zeroʳ p) ∙ (·-identityʳ p) ⟩
  𝟘ᶜ ∙ p                     ≡⟨⟩
  ([] *> ε) ∙ p ∎
  where open Tools.Reasoning.Equivalence Conₘ-setoid

liftSubstₘ-app (Ψ ⊙ η) γ p = begin
  liftSubstₘ (Ψ ⊙ η) *> (γ ∙ p)
     ≡⟨⟩
  (wk1Substₘ (Ψ ⊙ η) ⊙ (𝟘ᶜ ∙ 𝟙)) *> (γ ∙ p)
     ≡⟨⟩
  p ·ᶜ (𝟘ᶜ ∙ 𝟙) +ᶜ (wk1Substₘ (Ψ ⊙ η) *> γ)
     ≈⟨ +ᶜ-cong ((·ᶜ-zeroʳ p) ∙ (·-identityʳ p)) (wk1Substₘ-app (Ψ ⊙ η) γ) ⟩
  (𝟘ᶜ ∙ p) +ᶜ (((Ψ ⊙ η) *> γ) ∙ 𝟘)
     ≈⟨ (+ᶜ-identityˡ ((Ψ ⊙ η) *> γ)) ∙ (+-identityʳ p) ⟩
  ((Ψ ⊙ η) *> γ) ∙ p ∎
  where open Tools.Reasoning.Equivalence Conₘ-setoid

-- The identity matrix is a left identity to substitution application.
-- idSubstₘ *> γ ≡ γ.
-- Proof by identity of addition, multiplication and matrix multiplication,
-- zero of multiplication and lemma on the application of shifted substitution matrices.

*>-identityˡ : (γ : Conₘ n) → idSubstₘ *> γ ≈ᶜ γ
*>-identityˡ ε       = ≈ᶜ-refl
*>-identityˡ (γ ∙ p) = begin
  idSubstₘ *> (γ ∙ p) ≡⟨⟩
  ((p ·ᶜ 𝟘ᶜ) ∙ (p · 𝟙)) +ᶜ (wk1Substₘ idSubstₘ *> γ)
    ≈⟨ +ᶜ-cong ((·ᶜ-zeroʳ p) ∙ (·-identityʳ p)) (wk1Substₘ-app idSubstₘ γ) ⟩
  ((𝟘ᶜ ∙ p) +ᶜ ((idSubstₘ *> γ) ∙ 𝟘))
    ≈⟨ (+ᶜ-identityˡ _) ∙ (+-identityʳ p) ⟩
  (idSubstₘ *> γ) ∙ p
    ≈⟨ (*>-identityˡ γ) ∙ ≈-refl ⟩
  γ ∙ p ∎
  where open Tools.Reasoning.Equivalence Conₘ-setoid

-------------------------------
-- Well-formed substitutions --
-------------------------------

-- The substitution of a single (suitably well-used) variable is a
-- well-formed substitution.

wf-sgSubstₘ :
  ⌜ mo ⌝ ·ᶜ γ ▸[ mo ] u → sgSubstₘ γ ▶[ consᵐ mo mos ] sgSubst u
wf-sgSubstₘ {mo = mo} {γ = γ} γ▸u x0 = sub
  γ▸u
  (begin
     ⌜ mo ⌝ ·ᶜ γ +ᶜ idSubstₘ *> 𝟘ᶜ  ≈⟨ +ᶜ-congˡ (*>-identityˡ 𝟘ᶜ) ⟩
     ⌜ mo ⌝ ·ᶜ γ +ᶜ 𝟘ᶜ              ≈⟨ +ᶜ-identityʳ _ ⟩
     ⌜ mo ⌝ ·ᶜ γ                    ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
wf-sgSubstₘ {γ = γ} {mos = mos} _ (x +1) = sub
  var
  (begin
     𝟘 ·ᶜ γ +ᶜ idSubstₘ *> (𝟘ᶜ , x ≔ ⌜ mos x ⌝)  ≈⟨ +ᶜ-cong (·ᶜ-zeroˡ γ) (*>-identityˡ _) ⟩
     𝟘ᶜ +ᶜ (𝟘ᶜ , x ≔ ⌜ mos x ⌝)                  ≈⟨ +ᶜ-identityˡ _ ⟩
     𝟘ᶜ , x ≔ ⌜ mos x ⌝                          ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- The one-step weakening of a well-formed substitution is
-- well-formed.

wf-wk1Substₘ : (Ψ : Substₘ m n) (σ : Subst m n)
             → Ψ ▶[ mos ] σ → wk1Substₘ Ψ ▶[ mos ] wk1Subst σ
wf-wk1Substₘ Ψ σ Ψ▶σ x =
  sub (wkUsage (step id) (Ψ▶σ x)) (≤ᶜ-reflexive (wk1Substₘ-app Ψ _))

-- The one-step lift of a well-formed substitution is well-formed.

wf-liftSubstₘ :
  {Ψ : Substₘ m n} →
  Ψ ▶[ mos ] σ → liftSubstₘ Ψ ▶[ consᵐ mo mos ] liftSubst σ
wf-liftSubstₘ {mo = mo} {Ψ = Ψ} _ x0 = sub
  var
  (begin
     (⌜ mo ⌝ ·ᶜ 𝟘ᶜ ∙ ⌜ mo ⌝ · 𝟙) +ᶜ wk1Substₘ Ψ *> 𝟘ᶜ  ≈⟨ +ᶜ-cong (·ᶜ-zeroʳ _ ∙ ·-identityʳ _) (*>-zeroʳ (wk1Substₘ Ψ)) ⟩
     (𝟘ᶜ ∙ ⌜ mo ⌝) +ᶜ 𝟘ᶜ                               ≈⟨ +ᶜ-identityʳ _ ⟩
     𝟘ᶜ ∙ ⌜ mo ⌝                                       ≡⟨⟩
     𝟘ᶜ , x0 ≔ ⌜ mo ⌝                                  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
wf-liftSubstₘ {mos = mos} {Ψ = Ψ} Ψ▶σ (x +1) = sub
  (wf-wk1Substₘ Ψ _ Ψ▶σ x)
  (begin
    (𝟘 ·ᶜ 𝟘ᶜ ∙ 𝟘 · 𝟙) +ᶜ wk1Substₘ Ψ *> (𝟘ᶜ , x ≔ ⌜ mos x ⌝)  ≈⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _ ∙ ·-zeroˡ _) ⟩
    𝟘ᶜ +ᶜ wk1Substₘ Ψ *> (𝟘ᶜ , x ≔ ⌜ mos x ⌝)                 ≈⟨ +ᶜ-identityˡ _ ⟩
    wk1Substₘ Ψ *> (𝟘ᶜ , x ≔ ⌜ mos x ⌝)                       ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- The extension of a well-formed substitution with a suitably
-- well-used term is a well-formed substitution.

wf-consSubstₘ :
  {Ψ : Substₘ m n} {γ : Conₘ m} →
  Ψ ▶[ mos ] σ → ⌜ mo ⌝ ·ᶜ γ ▸[ mo ] t →
  Ψ ⊙ γ ▶[ consᵐ mo mos ] consSubst σ t
wf-consSubstₘ {mo = mo} {Ψ = Ψ} {γ = γ} Ψ▶σ γ▸t x0 = sub
  γ▸t
  (begin
     ⌜ mo ⌝ ·ᶜ γ +ᶜ Ψ *> 𝟘ᶜ  ≈⟨ +ᶜ-congˡ (*>-zeroʳ Ψ) ⟩
     ⌜ mo ⌝ ·ᶜ γ +ᶜ 𝟘ᶜ       ≈⟨ +ᶜ-identityʳ _ ⟩
     ⌜ mo ⌝ ·ᶜ γ             ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
wf-consSubstₘ {mos = mos} {Ψ = Ψ} {γ = γ} Ψ▶σ γ▸t (x +1) = sub
  (Ψ▶σ x)
  (begin
     𝟘 ·ᶜ γ +ᶜ Ψ *> (𝟘ᶜ , x ≔ ⌜ mos x ⌝) ≈⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
     𝟘ᶜ +ᶜ Ψ *> (𝟘ᶜ , x ≔ ⌜ mos x ⌝)     ≈⟨ +ᶜ-identityˡ _ ⟩
     Ψ *> (𝟘ᶜ , x ≔ ⌜ mos x ⌝)           ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- The tail of a well-formed substitution is a well-formed
-- substitution.

wf-tailSubstₘ :
  {Ψ : Substₘ m n} →
  (Ψ ⊙ γ) ▶[ mos ] σ → Ψ ▶[ tailᵐ mos ] tail σ
wf-tailSubstₘ Ψ▶σ x =
  sub (Ψ▶σ (x +1))
      (≤ᶜ-reflexive (≈ᶜ-sym (≈ᶜ-trans (+ᶜ-congʳ (·ᶜ-zeroˡ _)) (+ᶜ-identityˡ _))))

-- A preservation lemma for _▶[_]_.

▶-cong :
  (Ψ : Substₘ m n) →
  (∀ x → mos₁ x ≡ mos₂ x) → Ψ ▶[ mos₁ ] σ → Ψ ▶[ mos₂ ] σ
▶-cong Ψ mos₁≡mos₂ Ψ▶ x0 =
  PE.subst (λ mo → Ψ *> (𝟘ᶜ ∙ ⌜ mo ⌝) ▸[ mo ] _) (mos₁≡mos₂ x0) (Ψ▶ x0)
▶-cong {mos₁ = mos₁} {mos₂ = mos₂} (Ψ ⊙ γ) mos₁≡mos₂ Ψ⊙▶ (x +1) = sub
  (▶-cong Ψ (λ x → mos₁≡mos₂ (x +1))
    (λ x → sub (Ψ⊙▶ (x +1)) (≤ᶜ-reflexive (≈ᶜ-sym (lemma mos₁ x))))
    x)
  (≤ᶜ-reflexive (lemma mos₂ x))
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid

  lemma = λ mos x → begin
     𝟘 ·ᶜ γ +ᶜ Ψ *> (𝟘ᶜ , x ≔ ⌜ mos (x +1) ⌝)  ≈⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
     𝟘ᶜ +ᶜ Ψ *> (𝟘ᶜ , x ≔ ⌜ mos (x +1) ⌝)      ≈⟨ +ᶜ-identityˡ _ ⟩
     Ψ *> (𝟘ᶜ , x ≔ ⌜ mos (x +1) ⌝)            ∎

-- Another preservation lemma for _▶[_]_.

▶-≤ :
  (Ψ : Substₘ m n) →
  γ ≤ᶜ δ → Ψ ▶[ ⌞ γ ⌟ᶜ ] σ → Ψ ▶[ ⌞ δ ⌟ᶜ ] σ
▶-≤ Ψ γ≤δ Ψ▶ x = sub
  (▸-≤ (lookup-monotone _ γ≤δ)
     (sub (Ψ▶ x) (≤ᶜ-reflexive (·ᶜ-*>-𝟘ᶜ,≔𝟙 Ψ))))
  (≤ᶜ-reflexive (≈ᶜ-sym (·ᶜ-*>-𝟘ᶜ,≔𝟙 Ψ)))

-- A preservation lemma for _▶[_]_ that holds if 𝟘ᵐ is not allowed.

▶-without-𝟘ᵐ :
  (Ψ : Substₘ m n) →
  ¬ T 𝟘ᵐ-allowed →
  Ψ ▶[ mos₁ ] σ → Ψ ▶[ mos₂ ] σ
▶-without-𝟘ᵐ Ψ not-ok =
  ▶-cong Ψ (λ _ → Mode-propositional-without-𝟘ᵐ not-ok)

-- An inversion lemma for _▶[_]_ related to multiplication.

▶-⌞·⌟ :
  (Ψ : Substₘ m n) (γ : Conₘ n) →
  Ψ ▶[ ⌞ p ·ᶜ γ ⌟ᶜ ] σ →
  (p ≈ 𝟘 × T 𝟘ᵐ-allowed) ⊎ (Ψ ▶[ ⌞ γ ⌟ᶜ ] σ)
▶-⌞·⌟ {p = p} {σ = σ} Ψ γ Ψ▶ = 𝟘ᵐ-allowed-elim
  (λ ok → case is-𝟘? p of λ where
     (yes p≈𝟘) → inj₁ (p≈𝟘 , ok)
     (no p≉𝟘)  → inj₂ λ x →
       case ▸-⌞·⌟
         (sub (▸-cong (cong ⌞_⌟ (lookup-distrib-·ᶜ γ _ _)) (Ψ▶ x))
            (begin
               ⌜ ⌞ p · γ ⟨ x ⟩ ⌟ ⌝ ·ᶜ Ψ *> (𝟘ᶜ , x ≔ 𝟙)  ≈⟨ ·ᶜ-*>-𝟘ᶜ,≔𝟙 Ψ ⟩
               Ψ *> (𝟘ᶜ , x ≔ ⌜ ⌞ p · γ ⟨ x ⟩ ⌟ ⌝)       ≡˘⟨ cong (λ p → Ψ *> (𝟘ᶜ , x ≔ ⌜ ⌞ p ⌟ ⌝)) (lookup-distrib-·ᶜ γ _ _) ⟩
               Ψ *> (𝟘ᶜ , x ≔ ⌜ ⌞ p ·ᶜ γ ⌟ᶜ x ⌝)         ∎))
       of λ where
         (inj₂ ▸γx) → sub ▸γx (≤ᶜ-reflexive (≈ᶜ-sym (·ᶜ-*>-𝟘ᶜ,≔𝟙 Ψ)))
         (inj₁ ▸p)  → lemma _ _ _ (≉𝟘→⌞⌟≡𝟙ᵐ p≉𝟘) ▸p)
  (λ not-ok → inj₂ (▶-without-𝟘ᵐ Ψ not-ok Ψ▶))
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

  lemma :
    ∀ mo₁ mo₂ x →
    mo₁ ≡ 𝟙ᵐ →
    ⌜ mo₁ ⌝ ·ᶜ Ψ *> (𝟘ᶜ , x ≔ 𝟙) ▸[ mo₁ ] t →
    Ψ *> (𝟘ᶜ , x ≔ ⌜ mo₂ ⌝) ▸[ mo₂ ] t
  lemma 𝟙ᵐ 𝟘ᵐ x _ ▸t = sub (▸-𝟘 ▸t)
    (begin
       Ψ *> (𝟘ᶜ , x ≔ 𝟘)  ≡⟨ cong (Ψ *>_) 𝟘ᶜ,≔𝟘 ⟩
       Ψ *> 𝟘ᶜ            ≈⟨ *>-zeroʳ Ψ ⟩
       𝟘ᶜ                 ∎)
  lemma 𝟙ᵐ 𝟙ᵐ x _ ▸t = sub ▸t
    (begin
       Ψ *> (𝟘ᶜ , x ≔ 𝟙)       ≈˘⟨ ·ᶜ-identityˡ _ ⟩
       𝟙 ·ᶜ Ψ *> (𝟘ᶜ , x ≔ 𝟙)  ∎)

-- An inversion lemma for _▶[_]_ related to addition.

▶-⌞+ᶜ⌟ˡ :
  (Ψ : Substₘ m n) (γ : Conₘ n) →
  Ψ ▶[ ⌞ γ +ᶜ δ ⌟ᶜ ] σ → Ψ ▶[ ⌞ γ ⌟ᶜ ] σ
▶-⌞+ᶜ⌟ˡ {δ = δ} Ψ γ Ψ▶ x = sub
  (▸-⌞+⌟ˡ
     (sub (▸-cong (cong ⌞_⌟ (lookup-distrib-+ᶜ γ _ _)) (Ψ▶ x)) (begin
        ⌜ ⌞ γ ⟨ x ⟩ + δ ⟨ x ⟩ ⌟ ⌝ ·ᶜ Ψ *> (𝟘ᶜ , x ≔ 𝟙)  ≈⟨ ·ᶜ-*>-𝟘ᶜ,≔𝟙 Ψ ⟩
        Ψ *> (𝟘ᶜ , x ≔ ⌜ ⌞ γ ⟨ x ⟩ + δ ⟨ x ⟩ ⌟ ⌝)       ≡˘⟨ cong (λ p → Ψ *> (𝟘ᶜ , x ≔ ⌜ ⌞ p ⌟ ⌝)) (lookup-distrib-+ᶜ γ _ _) ⟩
        Ψ *> (𝟘ᶜ , x ≔ ⌜ ⌞ γ +ᶜ δ ⌟ᶜ x ⌝)               ∎)))
  (≤ᶜ-reflexive (≈ᶜ-sym (·ᶜ-*>-𝟘ᶜ,≔𝟙 Ψ)))
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- An inversion lemma for _▶[_]_ related to addition.

▶-⌞+ᶜ⌟ʳ :
  (Ψ : Substₘ m n) (γ : Conₘ n) →
  Ψ ▶[ ⌞ γ +ᶜ δ ⌟ᶜ ] σ → Ψ ▶[ ⌞ δ ⌟ᶜ ] σ
▶-⌞+ᶜ⌟ʳ {δ = δ} Ψ γ Ψ▶ =
  ▶-⌞+ᶜ⌟ˡ Ψ δ (▶-cong Ψ (⌞⌟ᶜ-cong (+ᶜ-comm γ _)) Ψ▶)

-- An inversion lemma for _▸[_]_ related to _*>_.

▸-⌞*>⌟ :
  (Ψ : Substₘ m n) →
  ⌜ ⌞ Ψ *> γ ⌟ᶜ y ⌝ ·ᶜ δ ▸[ ⌞ Ψ *> γ ⌟ᶜ y ] t →
  ⌜ ⌞ Ψ *> (𝟘ᶜ , x ≔ γ ⟨ x ⟩) ⌟ᶜ y ⌝ ·ᶜ δ
    ▸[ ⌞ Ψ *> (𝟘ᶜ , x ≔ γ ⟨ x ⟩) ⌟ᶜ y ] t
▸-⌞*>⌟ {γ = γ ∙ p} {y = y} {δ = δ} {t = t} {x = x0} (Ψ ⊙ η) ▸₁ = ▸₄
  where
  ▸₂ :
    ⌜ ⌞ (p ·ᶜ η) ⟨ y ⟩ + (Ψ *> γ) ⟨ y ⟩ ⌟ ⌝ ·ᶜ δ
      ▸[ ⌞ (p ·ᶜ η) ⟨ y ⟩ + (Ψ *> γ) ⟨ y ⟩ ⌟ ] t
  ▸₂ = PE.subst
    (λ γ → ⌜ ⌞ γ ⌟ ⌝ ·ᶜ _ ▸[ ⌞ γ ⌟ ] _)
    (lookup-distrib-+ᶜ (_ ·ᶜ η) _ _)
    ▸₁

  ▸₃ : ⌜ ⌞ p ·ᶜ η ⌟ᶜ y ⌝ ·ᶜ δ ▸[ ⌞ p ·ᶜ η ⌟ᶜ y ] t
  ▸₃ = ▸-⌞+⌟ˡ ▸₂

  ▸₄ :
    ⌜ ⌞ p ·ᶜ η +ᶜ (Ψ *> 𝟘ᶜ) ⌟ᶜ y ⌝ ·ᶜ δ
      ▸[ ⌞ p ·ᶜ η +ᶜ (Ψ *> 𝟘ᶜ) ⌟ᶜ y ] t
  ▸₄ = PE.subst
    (λ m → ⌜ m ⌝ ·ᶜ δ ▸[ m ] t)
    (⌞⌟-cong (lookup-cong (begin
       p ·ᶜ η               ≈˘⟨ +ᶜ-identityʳ _ ⟩
       p ·ᶜ η +ᶜ 𝟘ᶜ         ≈˘⟨ +ᶜ-congˡ (*>-zeroʳ Ψ) ⟩
       p ·ᶜ η +ᶜ (Ψ *> 𝟘ᶜ)  ∎)))
    ▸₃
    where
    open Tools.Reasoning.Equivalence Conₘ-setoid

▸-⌞*>⌟ {γ = γ ∙ p} {y = y} {δ = δ} {t = t} {x = x +1} (Ψ ⊙ η) ▸₁ = ▸₅
  where
  ▸₂ :
    ⌜ ⌞ (p ·ᶜ η) ⟨ y ⟩ + (Ψ *> γ) ⟨ y ⟩ ⌟ ⌝ ·ᶜ δ
      ▸[ ⌞ (p ·ᶜ η) ⟨ y ⟩ + (Ψ *> γ) ⟨ y ⟩ ⌟ ] t
  ▸₂ = PE.subst
    (λ γ → ⌜ ⌞ γ ⌟ ⌝ ·ᶜ _ ▸[ ⌞ γ ⌟ ] _)
    (lookup-distrib-+ᶜ (_ ·ᶜ η) _ _)
    ▸₁

  ▸₃ : ⌜ ⌞ Ψ *> γ ⌟ᶜ y ⌝ ·ᶜ δ ▸[ ⌞ Ψ *> γ ⌟ᶜ y ] t
  ▸₃ = ▸-⌞+⌟ʳ ▸₂

  ▸₄ : ⌜ ⌞ Ψ *> (𝟘ᶜ , x ≔ γ ⟨ x ⟩) ⌟ᶜ y ⌝ ·ᶜ δ
         ▸[ ⌞ Ψ *> (𝟘ᶜ , x ≔ γ ⟨ x ⟩) ⌟ᶜ y ] t
  ▸₄ = ▸-⌞*>⌟ Ψ ▸₃

  ▸₅ :
    ⌜ ⌞ 𝟘 ·ᶜ η +ᶜ (Ψ *> (𝟘ᶜ , x ≔ γ ⟨ x ⟩)) ⌟ᶜ y ⌝ ·ᶜ δ
      ▸[ ⌞ 𝟘 ·ᶜ η +ᶜ (Ψ *> (𝟘ᶜ , x ≔ γ ⟨ x ⟩)) ⌟ᶜ y ] t
  ▸₅ = PE.subst
    (λ m → ⌜ m ⌝ ·ᶜ δ ▸[ m ] t)
    (⌞⌟-cong (lookup-cong (begin
       Ψ *> (𝟘ᶜ , x ≔ γ ⟨ x ⟩)            ≈˘⟨ +ᶜ-identityˡ (Ψ *> _) ⟩
       𝟘ᶜ +ᶜ Ψ *> (𝟘ᶜ , x ≔ γ ⟨ x ⟩)      ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroˡ η) ⟩
       𝟘 ·ᶜ η +ᶜ Ψ *> (𝟘ᶜ , x ≔ γ ⟨ x ⟩)  ∎)))
    ▸₄
    where
    open Tools.Reasoning.Equivalence Conₘ-setoid

-- An inversion lemma for _▶[_]_ related to _*>_.

▶-⌞*>⌟ :
  (Ψ : Substₘ ℓ m) {Φ : Substₘ m n} →
  Ψ ▶[ ⌞ Φ *> γ ⌟ᶜ ] σ →
  Ψ ▶[ ⌞ Φ *> (𝟘ᶜ , x ≔ γ ⟨ x ⟩) ⌟ᶜ ] σ
▶-⌞*>⌟ {γ = γ} {x = x} Ψ {Φ = Φ} Ψ▶ y = sub
  (▸-⌞*>⌟ Φ (sub (Ψ▶ y) (≤ᶜ-reflexive (·ᶜ-*>-𝟘ᶜ,≔𝟙 Ψ))))
  (≤ᶜ-reflexive (≈ᶜ-sym (·ᶜ-*>-𝟘ᶜ,≔𝟙 Ψ)))

-- An inversion lemma for _▶[_]_ related to the meet operation.

▶-⌞∧ᶜ⌟ˡ :
  (Ψ : Substₘ m n) (γ : Conₘ n) →
  Ψ ▶[ ⌞ γ ∧ᶜ δ ⌟ᶜ ] σ → Ψ ▶[ ⌞ γ ⌟ᶜ ] σ
▶-⌞∧ᶜ⌟ˡ {δ = δ} Ψ γ Ψ▶ x = sub
  (▸-⌞∧⌟ˡ
     (sub (▸-cong (cong ⌞_⌟ (lookup-distrib-∧ᶜ γ _ _)) (Ψ▶ x)) (begin
        ⌜ ⌞ γ ⟨ x ⟩ ∧ δ ⟨ x ⟩ ⌟ ⌝ ·ᶜ Ψ *> (𝟘ᶜ , x ≔ 𝟙)  ≈⟨ ·ᶜ-*>-𝟘ᶜ,≔𝟙 Ψ ⟩
        Ψ *> (𝟘ᶜ , x ≔ ⌜ ⌞ γ ⟨ x ⟩ ∧ δ ⟨ x ⟩ ⌟ ⌝)       ≡˘⟨ cong (λ p → Ψ *> (𝟘ᶜ , x ≔ ⌜ ⌞ p ⌟ ⌝)) (lookup-distrib-∧ᶜ γ _ _) ⟩
        Ψ *> (𝟘ᶜ , x ≔ ⌜ ⌞ γ ∧ᶜ δ ⌟ᶜ x ⌝)               ∎)))
  (≤ᶜ-reflexive (≈ᶜ-sym (·ᶜ-*>-𝟘ᶜ,≔𝟙 Ψ)))
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- An inversion lemma for _▶[_]_ related to the meet operation.

▶-⌞∧ᶜ⌟ʳ :
  (Ψ : Substₘ m n) (γ : Conₘ n) →
  Ψ ▶[ ⌞ γ ∧ᶜ δ ⌟ᶜ ] σ → Ψ ▶[ ⌞ δ ⌟ᶜ ] σ
▶-⌞∧ᶜ⌟ʳ {δ = δ} Ψ γ Ψ▶ =
  ▶-⌞∧ᶜ⌟ˡ Ψ δ (▶-cong Ψ (⌞⌟ᶜ-cong (∧ᶜ-comm γ _)) Ψ▶)

-- An inversion lemma for _▶[_]_ related to the star operation.

▶-⌞⊛ᶜ⌟ˡ :
  (Ψ : Substₘ m n) (γ : Conₘ n) →
  Ψ ▶[ ⌞ γ ⊛ᶜ δ ▷ r ⌟ᶜ ] σ → Ψ ▶[ ⌞ γ ⌟ᶜ ] σ
▶-⌞⊛ᶜ⌟ˡ {δ = δ} {r = r} Ψ γ Ψ▶ x = sub
  (▸-⌞⊛⌟ˡ
     (sub (▸-cong (cong ⌞_⌟ (lookup-distrib-⊛ᶜ γ _ _ _)) (Ψ▶ x)) (begin
        ⌜ ⌞ γ ⟨ x ⟩ ⊛ δ ⟨ x ⟩ ▷ r ⌟ ⌝ ·ᶜ Ψ *> (𝟘ᶜ , x ≔ 𝟙)  ≡˘⟨ cong (λ p → ⌜ ⌞ p ⌟ ⌝ ·ᶜ _) (lookup-distrib-⊛ᶜ γ _ _ _) ⟩
        ⌜ ⌞ γ ⊛ᶜ δ ▷ r ⌟ᶜ x ⌝ ·ᶜ Ψ *> (𝟘ᶜ , x ≔ 𝟙)          ≈⟨ ·ᶜ-*>-𝟘ᶜ,≔𝟙 Ψ ⟩
        Ψ *> (𝟘ᶜ , x ≔ ⌜ ⌞ γ ⊛ᶜ δ ▷ r ⌟ᶜ x ⌝)               ∎)))
  (≤ᶜ-reflexive (≈ᶜ-sym (·ᶜ-*>-𝟘ᶜ,≔𝟙 Ψ)))
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- An inversion lemma for _▶[_]_ related to the star operation.

▶-⌞⊛ᶜ⌟ʳ :
  (Ψ : Substₘ m n) (γ : Conₘ n) →
  Ψ ▶[ ⌞ γ ⊛ᶜ δ ▷ r ⌟ᶜ ] σ → Ψ ▶[ ⌞ δ ⌟ᶜ ] σ
▶-⌞⊛ᶜ⌟ʳ {δ = δ} {r = r} Ψ γ Ψ▶ x = sub
  (▸-⌞⊛⌟ʳ
     (sub (▸-cong (cong ⌞_⌟ (lookup-distrib-⊛ᶜ γ _ _ _)) (Ψ▶ x)) (begin
        ⌜ ⌞ γ ⟨ x ⟩ ⊛ δ ⟨ x ⟩ ▷ r ⌟ ⌝ ·ᶜ Ψ *> (𝟘ᶜ , x ≔ 𝟙)  ≡˘⟨ cong (λ p → ⌜ ⌞ p ⌟ ⌝ ·ᶜ _) (lookup-distrib-⊛ᶜ γ _ _ _) ⟩
        ⌜ ⌞ γ ⊛ᶜ δ ▷ r ⌟ᶜ x ⌝ ·ᶜ Ψ *> (𝟘ᶜ , x ≔ 𝟙)          ≈⟨ ·ᶜ-*>-𝟘ᶜ,≔𝟙 Ψ ⟩
        Ψ *> (𝟘ᶜ , x ≔ ⌜ ⌞ γ ⊛ᶜ δ ▷ r ⌟ᶜ x ⌝)               ∎)))
  (≤ᶜ-reflexive (≈ᶜ-sym (·ᶜ-*>-𝟘ᶜ,≔𝟙 Ψ)))
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

---------------------------------------
-- Substitution lemma for modalities --
---------------------------------------

-- A substitution lemma for the mode 𝟘ᵐ[ ok ]: if σ is well-formed and
-- t is well-used, then U.subst σ t is well-used in the mode 𝟘ᵐ[ ok ],
-- with no usages.

substₘ-lemma₀ :
  ∀ ⦃ ok ⦄ (Ψ : Substₘ m n) →
  Ψ ▶[ mos ] σ → γ ▸[ mo ] t → 𝟘ᶜ ▸[ 𝟘ᵐ[ ok ] ] U.subst σ t
substₘ-lemma₀ _ _ Uₘ =
  Uₘ

substₘ-lemma₀ _ _ ℕₘ =
  ℕₘ

substₘ-lemma₀ _ _ Emptyₘ =
  Emptyₘ

substₘ-lemma₀ _ _ Unitₘ =
  Unitₘ

substₘ-lemma₀ Ψ Ψ▶σ (Πₘ {p = p} γ▸F δ▸G) = sub
  (Πₘ (substₘ-lemma₀ Ψ Ψ▶σ γ▸F)
     (sub (substₘ-lemma₀ (liftSubstₘ Ψ) (wf-liftSubstₘ {mo = 𝟘ᵐ} Ψ▶σ)
             δ▸G)
        (≤ᶜ-reflexive (≈ᶜ-refl ∙ ·-zeroˡ _))))
  (≤ᶜ-reflexive (≈ᶜ-sym (+ᶜ-identityˡ _)))

substₘ-lemma₀ Ψ Ψ▶σ (Σₘ γ▸F δ▸G) = sub
  (Σₘ (substₘ-lemma₀ Ψ Ψ▶σ γ▸F)
     (sub (substₘ-lemma₀ (liftSubstₘ Ψ) (wf-liftSubstₘ {mo = 𝟘ᵐ} Ψ▶σ)
             δ▸G)
        (≤ᶜ-reflexive (≈ᶜ-refl ∙ ·-zeroˡ _))))
  (≤ᶜ-reflexive (≈ᶜ-sym (+ᶜ-identityˡ _)))

substₘ-lemma₀ Ψ Ψ▶σ (var {x = x}) = ▸-𝟘 (Ψ▶σ x)

substₘ-lemma₀ Ψ Ψ▶σ (lamₘ γ▸t) = lamₘ
  (sub (substₘ-lemma₀ (liftSubstₘ Ψ) (wf-liftSubstₘ {mo = 𝟘ᵐ} Ψ▶σ) γ▸t)
     (≤ᶜ-reflexive (≈ᶜ-refl ∙ ·-zeroˡ _)))

substₘ-lemma₀ Ψ Ψ▶σ (_∘ₘ_ {p = p} γ▸t δ▸u) = sub
  (substₘ-lemma₀ Ψ Ψ▶σ γ▸t ∘ₘ
   substₘ-lemma₀ Ψ Ψ▶σ δ▸u)
  (begin
     𝟘ᶜ             ≈˘⟨ +ᶜ-identityˡ _ ⟩
     𝟘ᶜ +ᶜ 𝟘ᶜ       ≈˘⟨ +ᶜ-congˡ (·ᶜ-zeroʳ _) ⟩
     𝟘ᶜ +ᶜ p ·ᶜ 𝟘ᶜ  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

substₘ-lemma₀ Ψ Ψ▶σ (prodᵣₘ {p = p} γ▸t δ▸u PE.refl) = sub
  (prodᵣₘ (substₘ-lemma₀ Ψ Ψ▶σ γ▸t) (substₘ-lemma₀ Ψ Ψ▶σ δ▸u)
     PE.refl)
  (begin
     𝟘ᶜ             ≈˘⟨ ·ᶜ-zeroʳ _ ⟩
     p ·ᶜ 𝟘ᶜ        ≈˘⟨ +ᶜ-identityʳ _ ⟩
     p ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

substₘ-lemma₀ Ψ Ψ▶σ (prodₚₘ {p = p} γ▸t γ▸u) = sub
  (prodₚₘ (substₘ-lemma₀ Ψ Ψ▶σ γ▸t) (substₘ-lemma₀ Ψ Ψ▶σ γ▸u))
  (begin
     𝟘ᶜ             ≈˘⟨ ∧ᶜ-idem _ ⟩
     𝟘ᶜ ∧ᶜ 𝟘ᶜ       ≈˘⟨ ∧ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
     p ·ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

substₘ-lemma₀ Ψ Ψ▶σ (fstₘ m γ▸t PE.refl ok) =
  fstₘ 𝟘ᵐ (substₘ-lemma₀ Ψ Ψ▶σ γ▸t) PE.refl ok

substₘ-lemma₀ Ψ Ψ▶σ (sndₘ γ▸t) =
  sndₘ (substₘ-lemma₀ Ψ Ψ▶σ γ▸t)

substₘ-lemma₀ Ψ Ψ▶σ (prodrecₘ {r = r} γ▸t δ▸u P) = sub
  (prodrecₘ (substₘ-lemma₀ Ψ Ψ▶σ γ▸t)
     (sub (substₘ-lemma₀ (liftSubstₘ (liftSubstₘ Ψ))
             (wf-liftSubstₘ {mo = 𝟘ᵐ} (wf-liftSubstₘ {mo = 𝟘ᵐ} Ψ▶σ))
             δ▸u)
        (≤ᶜ-reflexive (≈ᶜ-refl ∙ ·-zeroˡ _ ∙ ·-zeroˡ _)))
     P)
  (begin
     𝟘ᶜ             ≈˘⟨ +ᶜ-identityˡ _ ⟩
     𝟘ᶜ +ᶜ 𝟘ᶜ       ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
     r ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

substₘ-lemma₀ _ _ zeroₘ =
  zeroₘ

substₘ-lemma₀ Ψ Ψ▶σ (sucₘ γ▸t) =
  sucₘ (substₘ-lemma₀ Ψ Ψ▶σ γ▸t)

substₘ-lemma₀ Ψ Ψ▶σ (natrecₘ {p = p} {r = r} γ▸z δ▸s η▸n) = sub
  (natrecₘ (substₘ-lemma₀ Ψ Ψ▶σ γ▸z)
     (sub (substₘ-lemma₀ (liftSubstₘ (liftSubstₘ Ψ))
             (wf-liftSubstₘ {mo = 𝟘ᵐ} (wf-liftSubstₘ {mo = 𝟘ᵐ} Ψ▶σ))
             δ▸s)
        (≤ᶜ-reflexive (≈ᶜ-refl ∙ ·-zeroˡ _ ∙ ·-zeroˡ _)))
     (substₘ-lemma₀ Ψ Ψ▶σ η▸n))
  (begin
     𝟘ᶜ                               ≈˘⟨ ⊛ᶜ-idem-𝟘ᶜ _ ⟩
     𝟘ᶜ ⊛ᶜ 𝟘ᶜ ▷ r                     ≈˘⟨ ⊛ᵣᶜ-congˡ (·ᶜ-zeroʳ _) ⟩
     𝟘ᶜ ⊛ᶜ p ·ᶜ 𝟘ᶜ ▷ r                ≈˘⟨ ⊛ᵣᶜ-cong (∧ᶜ-idem _) (+ᶜ-identityˡ _) ⟩
     (𝟘ᶜ ∧ᶜ 𝟘ᶜ) ⊛ᶜ 𝟘ᶜ +ᶜ p ·ᶜ 𝟘ᶜ ▷ r  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

substₘ-lemma₀ Ψ Ψ▶σ (Emptyrecₘ γ▸t) =
  sub (Emptyrecₘ (substₘ-lemma₀ Ψ Ψ▶σ γ▸t))
    (≤ᶜ-reflexive (≈ᶜ-sym (·ᶜ-zeroʳ _)))

substₘ-lemma₀ _ _ starₘ =
  starₘ

substₘ-lemma₀ Ψ Ψ▶σ (sub γ▸t _) =
  substₘ-lemma₀ Ψ Ψ▶σ γ▸t

private

  -- Some simple lemmas used in the proof of the substitution lemma
  -- below.

  ≈𝟘→𝟘ᵐ≡ᵐ· : ∀ ⦃ ok ⦄ mo → p ≈ 𝟘 → 𝟘ᵐ[ ok ] ≡ mo ᵐ· p
  ≈𝟘→𝟘ᵐ≡ᵐ· {p = p} mo p≈𝟘 =
    𝟘ᵐ       ≡˘⟨ 𝟘ᵐ?≡𝟘ᵐ ⟩
    𝟘ᵐ?      ≡˘⟨ ᵐ·-zeroʳ mo ⟩
    mo ᵐ· 𝟘  ≡˘⟨ ᵐ·-cong mo p≈𝟘 ⟩
    mo ᵐ· p  ∎
    where
    open Tools.Reasoning.PropositionalEquality

  ≈𝟘→·*>≈·𝟘 : (Ψ : Substₘ m n) → p ≈ 𝟘 → p ·ᶜ Ψ *> δ ≈ᶜ p ·ᶜ 𝟘ᶜ
  ≈𝟘→·*>≈·𝟘 {p = p} {δ = δ} Ψ p≈𝟘 = begin
    p ·ᶜ Ψ *> δ  ≈⟨ ·ᶜ-congʳ p≈𝟘 ⟩
    𝟘 ·ᶜ Ψ *> δ  ≈⟨ ·ᶜ-zeroˡ _ ⟩
    𝟘ᶜ           ≈˘⟨ ·ᶜ-zeroʳ _ ⟩
    p ·ᶜ 𝟘ᶜ      ∎
    where
    open Tools.Reasoning.Equivalence Conₘ-setoid

  *>∙∙≤liftSubst-listSubst*>∙∙ :
    (Ψ : Substₘ m n) →
    (Ψ *> δ) ∙ p ∙ q ≤ᶜ liftSubstₘ (liftSubstₘ Ψ) *> (δ ∙ p ∙ q)
  *>∙∙≤liftSubst-listSubst*>∙∙ {δ = δ} {p = p} {q = q} Ψ = begin
    (Ψ *> δ) ∙ p ∙ q                           ≈˘⟨ +ᶜ-identityˡ _ ∙ +-identityʳ _ ∙ ≈-refl ⟩
    (𝟘ᶜ +ᶜ Ψ *> δ) ∙ (p + 𝟘) ∙ q               ≈˘⟨ (+ᶜ-cong (·ᶜ-zeroʳ _ ∙ ·-identityʳ _) (wk1Substₘ-app Ψ _)) ∙ ≈-refl ⟩
    (p ·ᶜ 𝟘ᶜ ∙ p · 𝟙) +ᶜ wk1Substₘ Ψ *> δ ∙ q  ≈˘⟨ liftSubstₘ-app (liftSubstₘ Ψ) (_ ∙ _) _ ⟩
    liftSubstₘ (liftSubstₘ Ψ) *> (δ ∙ p ∙ q)   ∎
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- The main substitution lemma.

substₘ-lemma :
  (Ψ : Substₘ m n) →
  Ψ ▶[ ⌞ γ ⌟ᶜ ] σ → γ ▸[ mo ] t → substₘ Ψ γ ▸[ mo ] U.subst σ t
substₘ-lemma Ψ _ Uₘ =
  sub Uₘ (≤ᶜ-reflexive (*>-zeroʳ Ψ))

substₘ-lemma Ψ _ ℕₘ =
  sub ℕₘ (≤ᶜ-reflexive (*>-zeroʳ Ψ))

substₘ-lemma Ψ _ Emptyₘ =
  sub Emptyₘ (≤ᶜ-reflexive (*>-zeroʳ Ψ))

substₘ-lemma Ψ _ Unitₘ =
  sub Unitₘ (≤ᶜ-reflexive (*>-zeroʳ Ψ))

substₘ-lemma Ψ Ψ▶σ (Πₘ {γ = γ} γ▸F δ▸G) = sub
  (Πₘ (substₘ-lemma Ψ (▶-⌞+ᶜ⌟ˡ Ψ γ Ψ▶σ) γ▸F)
     (sub (substₘ-lemma (liftSubstₘ Ψ)
             (▶-cong (liftSubstₘ Ψ)
                (λ where
                   (_ +1) → PE.refl
                   x0     → PE.refl)
                (wf-liftSubstₘ (▶-⌞+ᶜ⌟ʳ Ψ γ Ψ▶σ)))
             δ▸G)
        (≤ᶜ-reflexive (≈ᶜ-sym (liftSubstₘ-app Ψ _ _)))))
  (≤ᶜ-reflexive (*>-distrib-+ᶜ Ψ _ _))

substₘ-lemma Ψ Ψ▶σ (Σₘ {γ = γ} γ▸F δ▸G) = sub
  (Σₘ (substₘ-lemma Ψ (▶-⌞+ᶜ⌟ˡ Ψ γ Ψ▶σ) γ▸F)
     (sub (substₘ-lemma (liftSubstₘ Ψ)
             (▶-cong (liftSubstₘ Ψ)
                (λ where
                   (_ +1) → PE.refl
                   x0     → PE.refl)
                (wf-liftSubstₘ (▶-⌞+ᶜ⌟ʳ Ψ γ Ψ▶σ)))
             δ▸G)
        (≤ᶜ-reflexive (≈ᶜ-sym (liftSubstₘ-app Ψ _ _)))))
  (≤ᶜ-reflexive (*>-distrib-+ᶜ Ψ _ _))

substₘ-lemma {σ = σ} {mo = mo} Ψ Ψ▶σ (var {x = x}) =
  lemma₂ mo (is-𝟘? 𝟙) lemma₁
  where
  lemma₁ : Ψ *> (𝟘ᶜ , x ≔ ⌜ mo ⌝) ▸[ ⌞ ⌜ mo ⌝ ⌟ ] σ x
  lemma₁ = sub
    (▸-cong (let open Tools.Reasoning.PropositionalEquality in
               ⌞ (𝟘ᶜ , x ≔ ⌜ mo ⌝) ⟨ x ⟩ ⌟  ≡⟨ cong ⌞_⌟ (update-lookup 𝟘ᶜ x) ⟩
               ⌞ ⌜ mo ⌝ ⌟                   ∎)
       (Ψ▶σ x))
    (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
       Ψ *> (𝟘ᶜ , x ≔ ⌜ mo ⌝)                           ≈˘⟨ *>-cong Ψ (update-congʳ (⌜⌞⌜⌝⌟⌝ mo)) ⟩
       Ψ *> (𝟘ᶜ , x ≔ ⌜ ⌞ ⌜ mo ⌝ ⌟ ⌝)                   ≡˘⟨ cong (λ p → Ψ *> (_ , _ ≔ ⌜ ⌞ p ⌟ ⌝)) (update-lookup 𝟘ᶜ x) ⟩
       Ψ *> (𝟘ᶜ , x ≔ ⌜ ⌞ (𝟘ᶜ , x ≔ ⌜ mo ⌝) ⟨ x ⟩ ⌟ ⌝)  ∎)

  lemma₂ :
    ∀ mo → Dec (𝟙 ≈ 𝟘) →
    Ψ *> (𝟘ᶜ , x ≔ ⌜ mo ⌝) ▸[ ⌞ ⌜ mo ⌝ ⌟ ] σ x →
    Ψ *> (𝟘ᶜ , x ≔ ⌜ mo ⌝) ▸[ mo ] σ x
  lemma₂ 𝟘ᵐ _         = ▸-cong ⌞𝟘⌟
  lemma₂ 𝟙ᵐ (no 𝟙≉𝟘)  = ▸-cong (⌞⌜⌝⌟ 𝟙≉𝟘 _)
  lemma₂ 𝟙ᵐ (yes 𝟙≈𝟘) = ▸-𝟙≈𝟘 𝟙≈𝟘

substₘ-lemma {mo = mo} Ψ Ψ▶σ (lamₘ {p = p} γ▸t) = lamₘ
  (sub (substₘ-lemma (liftSubstₘ Ψ)
          (▶-cong (liftSubstₘ Ψ)
             (λ where
                (_ +1) → PE.refl
                x0     →
                  mo ᵐ· p         ≡˘⟨ ⌞⌜⌝·⌟ mo ⟩
                  ⌞ ⌜ mo ⌝ · p ⌟  ∎)
             (wf-liftSubstₘ Ψ▶σ))
          γ▸t)
     (≤ᶜ-reflexive (≈ᶜ-sym (liftSubstₘ-app Ψ _ _))))
  where
  open Tools.Reasoning.PropositionalEquality

substₘ-lemma
  {σ = σ} {mo = mo} Ψ Ψ▶σ
  (_∘ₘ_ {γ = γ} {t = t} {δ = δ} {p = p} {u = u} γ▸t δ▸u) =
  case ▶-⌞·⌟ Ψ δ (▶-⌞+ᶜ⌟ʳ Ψ γ Ψ▶σ) of λ where
    (inj₂ Ψ▶σ)        → lemma (substₘ-lemma Ψ Ψ▶σ δ▸u) ≈ᶜ-refl
    (inj₁ (p≈𝟘 , ok)) → lemma
      (▸-cong (≈𝟘→𝟘ᵐ≡ᵐ· ⦃ ok = ok ⦄ mo p≈𝟘)
         (substₘ-lemma₀ ⦃ ok = ok ⦄ Ψ Ψ▶σ δ▸u))
      (≈𝟘→·*>≈·𝟘 Ψ p≈𝟘)
  where
  lemma :
    η ▸[ mo ᵐ· p ] U.subst σ u →
    p ·ᶜ Ψ *> δ ≈ᶜ p ·ᶜ η →
    Ψ *> (γ +ᶜ p ·ᶜ δ) ▸[ mo ] U.subst σ (t ∘⟨ p ⟩ u)
  lemma {η = η} hyp₁ hyp₂ = sub
    (substₘ-lemma Ψ (▶-⌞+ᶜ⌟ˡ Ψ γ Ψ▶σ) γ▸t ∘ₘ hyp₁)
    (begin
       Ψ *> (γ +ᶜ p ·ᶜ δ)       ≈⟨ *>-distrib-+ᶜ Ψ _ _ ⟩
       Ψ *> γ +ᶜ Ψ *> (p ·ᶜ δ)  ≈⟨ +ᶜ-congˡ (*>-distrib-·ᶜ Ψ _ _) ⟩
       Ψ *> γ +ᶜ p ·ᶜ Ψ *> δ    ≈⟨ +ᶜ-congˡ hyp₂ ⟩
       Ψ *> γ +ᶜ p ·ᶜ η         ∎)
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset

substₘ-lemma
  {σ = σ} {mo = mo} Ψ Ψ▶σ
  (prodᵣₘ {γ = γ} {p = p} {t = t} {δ = δ} {u = u} γ▸t δ▸u PE.refl) =
  case ▶-⌞·⌟ Ψ γ (▶-⌞+ᶜ⌟ˡ Ψ (_ ·ᶜ γ) Ψ▶σ) of λ where
    (inj₂ Ψ▶σ)        → lemma (substₘ-lemma Ψ Ψ▶σ γ▸t) ≈ᶜ-refl
    (inj₁ (p≈𝟘 , ok)) → lemma
      (▸-cong (≈𝟘→𝟘ᵐ≡ᵐ· ⦃ ok = ok ⦄ mo p≈𝟘)
         (substₘ-lemma₀ ⦃ ok = ok ⦄ Ψ Ψ▶σ γ▸t))
      (≈𝟘→·*>≈·𝟘 Ψ p≈𝟘)
  where
  lemma :
    η ▸[ mo ᵐ· p ] U.subst σ t →
    p ·ᶜ Ψ *> γ ≈ᶜ p ·ᶜ η →
    Ψ *> (p ·ᶜ γ +ᶜ δ) ▸[ mo ] U.subst σ (prodᵣ p t u)
  lemma {η = η} hyp₁ hyp₂ = sub
    (prodᵣₘ hyp₁ (substₘ-lemma Ψ (▶-⌞+ᶜ⌟ʳ Ψ (_ ·ᶜ γ) Ψ▶σ) δ▸u) PE.refl)
    (begin
       Ψ *> (p ·ᶜ γ +ᶜ δ)       ≈⟨ *>-distrib-+ᶜ Ψ _ _ ⟩
       Ψ *> (p ·ᶜ γ) +ᶜ Ψ *> δ  ≈⟨ +ᶜ-congʳ (*>-distrib-·ᶜ Ψ _ _) ⟩
       p ·ᶜ Ψ *> γ +ᶜ Ψ *> δ    ≈⟨ +ᶜ-congʳ hyp₂ ⟩
       p ·ᶜ η +ᶜ Ψ *> δ         ∎)
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset

substₘ-lemma
  {σ = σ} {mo = mo} Ψ Ψ▶σ
  (prodₚₘ {γ = γ} {p = p} {t = t} {δ = δ} {u = u} γ▸t δ▸u) =
  case ▶-⌞·⌟ Ψ γ (▶-⌞∧ᶜ⌟ˡ Ψ (_ ·ᶜ γ) Ψ▶σ) of λ where
    (inj₂ Ψ▶σ)        → lemma (substₘ-lemma Ψ Ψ▶σ γ▸t) ≈ᶜ-refl
    (inj₁ (p≈𝟘 , ok)) → lemma
      (▸-cong (≈𝟘→𝟘ᵐ≡ᵐ· ⦃ ok = ok ⦄ mo p≈𝟘)
         (substₘ-lemma₀ ⦃ ok = ok ⦄ Ψ Ψ▶σ γ▸t))
      (≈𝟘→·*>≈·𝟘 Ψ p≈𝟘)
  where
  lemma :
    η ▸[ mo ᵐ· p ] U.subst σ t →
    p ·ᶜ Ψ *> γ ≈ᶜ p ·ᶜ η →
    Ψ *> (p ·ᶜ γ ∧ᶜ δ) ▸[ mo ] U.subst σ (prodₚ p t u)
  lemma {η = η} hyp₁ hyp₂ = sub
    (prodₚₘ hyp₁ (substₘ-lemma Ψ (▶-⌞∧ᶜ⌟ʳ Ψ (_ ·ᶜ γ) Ψ▶σ) δ▸u))
    (begin
       Ψ *> (p ·ᶜ γ ∧ᶜ δ)       ≤⟨ *>-sub-distrib-∧ᶜ Ψ _ _ ⟩
       Ψ *> (p ·ᶜ γ) ∧ᶜ Ψ *> δ  ≈⟨ ∧ᶜ-congʳ (*>-distrib-·ᶜ Ψ _ _) ⟩
       p ·ᶜ Ψ *> γ ∧ᶜ Ψ *> δ    ≈⟨ ∧ᶜ-congʳ hyp₂ ⟩
       p ·ᶜ η ∧ᶜ Ψ *> δ         ∎)
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset

substₘ-lemma Ψ Ψ▶σ (fstₘ m γ▸t PE.refl ok) =
  fstₘ m (substₘ-lemma Ψ Ψ▶σ γ▸t) PE.refl ok

substₘ-lemma Ψ Ψ▶σ (sndₘ γ▸t) =
  sndₘ (substₘ-lemma Ψ Ψ▶σ γ▸t)

substₘ-lemma
  {σ = σ} {mo = mo} Ψ Ψ▶σ
  (prodrecₘ {γ = γ} {r = r} {t = t} {δ = δ} {p = p} {u = u} {A = A}
     γ▸t δ▸u P) =
  case ▶-⌞·⌟ Ψ γ (▶-⌞+ᶜ⌟ˡ Ψ (_ ·ᶜ γ) Ψ▶σ) of λ where
    (inj₂ Ψ▶σ)        → lemma (substₘ-lemma Ψ Ψ▶σ γ▸t) ≈ᶜ-refl
    (inj₁ (p≈𝟘 , ok)) → lemma
      (▸-cong (≈𝟘→𝟘ᵐ≡ᵐ· ⦃ ok = ok ⦄ mo p≈𝟘)
         (substₘ-lemma₀ ⦃ ok = ok ⦄ Ψ Ψ▶σ γ▸t))
      (≈𝟘→·*>≈·𝟘 Ψ p≈𝟘)
  where
  lemma :
    η ▸[ mo ᵐ· r ] U.subst σ t →
    r ·ᶜ Ψ *> γ ≈ᶜ r ·ᶜ η →
    Ψ *> (r ·ᶜ γ +ᶜ δ) ▸[ mo ] U.subst σ (prodrec r p A t u)
  lemma {η = η} hyp₁ hyp₂ = sub
    (prodrecₘ hyp₁
       (sub (substₘ-lemma (liftSubstₘ (liftSubstₘ Ψ))
               (▶-cong (liftSubstₘ (liftSubstₘ Ψ))
                  (λ where
                     x0          → PE.refl
                     (x0 +1)     → PE.refl
                     ((_ +1) +1) → PE.refl)
                  (wf-liftSubstₘ
                     (wf-liftSubstₘ (▶-⌞+ᶜ⌟ʳ Ψ (_ ·ᶜ γ) Ψ▶σ))))
               δ▸u)
          (*>∙∙≤liftSubst-listSubst*>∙∙ Ψ))
       P)
    (begin
       Ψ *> (r ·ᶜ γ +ᶜ δ)       ≈⟨ *>-distrib-+ᶜ Ψ _ _ ⟩
       Ψ *> (r ·ᶜ γ) +ᶜ Ψ *> δ  ≈⟨ +ᶜ-congʳ (*>-distrib-·ᶜ Ψ _ _) ⟩
       r ·ᶜ Ψ *> γ +ᶜ Ψ *> δ    ≈⟨ +ᶜ-congʳ hyp₂ ⟩
       r ·ᶜ η +ᶜ Ψ *> δ         ∎)
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset

substₘ-lemma Ψ _ zeroₘ =
  sub zeroₘ (≤ᶜ-reflexive (*>-zeroʳ Ψ))

substₘ-lemma Ψ Ψ▶σ (sucₘ γ▸t) =
  sucₘ (substₘ-lemma Ψ Ψ▶σ γ▸t)

substₘ-lemma
  {mo = mo} Ψ Ψ▶σ
  (natrecₘ {γ = γ} {δ = δ} {p = p} {r = r} {η = η} γ▸z δ▸s η▸n) = sub
  (natrecₘ
     (substₘ-lemma Ψ (▶-⌞∧ᶜ⌟ˡ Ψ γ (▶-⌞⊛ᶜ⌟ˡ Ψ (γ ∧ᶜ _) Ψ▶σ)) γ▸z)
     (sub
       (substₘ-lemma (liftSubstₘ (liftSubstₘ Ψ))
          (▶-cong (liftSubstₘ (liftSubstₘ Ψ))
             (λ where
                x0          → PE.refl
                (x0 +1)     → PE.refl
                ((_ +1) +1) → PE.refl)
             (wf-liftSubstₘ
                (wf-liftSubstₘ (▶-⌞+ᶜ⌟ˡ Ψ δ (▶-⌞⊛ᶜ⌟ʳ Ψ (γ ∧ᶜ _) Ψ▶σ)))))
          δ▸s)
       (*>∙∙≤liftSubst-listSubst*>∙∙ Ψ))
     (substₘ-lemma Ψ (▶-⌞∧ᶜ⌟ʳ Ψ γ (▶-⌞⊛ᶜ⌟ˡ Ψ (γ ∧ᶜ _) Ψ▶σ)) η▸n))
  (begin
     Ψ *> ((γ ∧ᶜ η) ⊛ᶜ (δ +ᶜ p ·ᶜ η) ▷ r)                 ≤⟨ *>-sub-distrib-⊛ᶜ Ψ _ _ _ ⟩
     (Ψ *> (γ ∧ᶜ η)) ⊛ᶜ (Ψ *> (δ +ᶜ p ·ᶜ η)) ▷ r          ≈⟨ ⊛ᵣᶜ-congˡ (*>-distrib-+ᶜ Ψ _ _) ⟩
     (Ψ *> (γ ∧ᶜ η)) ⊛ᶜ (Ψ *> δ +ᶜ Ψ *> (p ·ᶜ η)) ▷ r     ≤⟨ ⊛ᶜ-monotoneʳ (*>-sub-distrib-∧ᶜ Ψ _ _) ⟩
     (Ψ *> γ ∧ᶜ Ψ *> η) ⊛ᶜ (Ψ *> δ +ᶜ Ψ *> (p ·ᶜ η)) ▷ r  ≈⟨ ⊛ᵣᶜ-congˡ (+ᶜ-congˡ (*>-distrib-·ᶜ Ψ _ _)) ⟩
     (Ψ *> γ ∧ᶜ Ψ *> η) ⊛ᶜ (Ψ *> δ +ᶜ p ·ᶜ Ψ *> η) ▷ r    ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

substₘ-lemma {mo = mo} Ψ Ψ▶σ (Emptyrecₘ {γ = γ} {p = p} γ▸t) =
  case ▶-⌞·⌟ Ψ γ Ψ▶σ of λ where
    (inj₂ Ψ▶σ) → sub
      (Emptyrecₘ (substₘ-lemma Ψ Ψ▶σ γ▸t))
      (≤ᶜ-reflexive (*>-distrib-·ᶜ Ψ _ _))
    (inj₁ (p≈𝟘 , ok)) → sub
      (Emptyrecₘ (▸-cong (≈𝟘→𝟘ᵐ≡ᵐ· ⦃ ok = ok ⦄ mo p≈𝟘)
                    (substₘ-lemma₀ ⦃ ok = ok ⦄ Ψ Ψ▶σ γ▸t)))
      (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
         Ψ *> (p ·ᶜ γ)  ≈⟨ *>-distrib-·ᶜ Ψ _ _ ⟩
         p ·ᶜ Ψ *> γ    ≈⟨ ≈𝟘→·*>≈·𝟘 Ψ p≈𝟘 ⟩
         p ·ᶜ 𝟘ᶜ        ∎)

substₘ-lemma Ψ Ψ▶σ starₘ = sub
  starₘ
  (≤ᶜ-reflexive (*>-zeroʳ Ψ))

substₘ-lemma Ψ Ψ▶σ (sub γ▸t γ≤δ) = sub
  (substₘ-lemma Ψ (▶-≤ Ψ γ≤δ Ψ▶σ) γ▸t)
  (*>-monotone Ψ γ≤δ)

-- A substitution lemma for single substitutions.

sgSubstₘ-lemma₁ :
  γ ∙ ⌜ mo ⌝ · p ▸[ mo ] t → δ ▸[ mo ᵐ· p ] u →
  γ +ᶜ (⌜ mo ⌝ · p) ·ᶜ δ ▸[ mo ] t [ u ]
sgSubstₘ-lemma₁ {γ = γ} {mo = mo} {p = p} {δ = δ} γ▸t δ▸u = sub
  (substₘ-lemma (sgSubstₘ δ)
     (▶-cong (sgSubstₘ δ)
        (λ where
           (_ +1) → PE.refl
           x0     → PE.sym (⌞⌜⌝·⌟ mo))
        (wf-sgSubstₘ (▸-·′ δ▸u)))
     γ▸t)
  (begin
     γ +ᶜ (⌜ mo ⌝ · p) ·ᶜ δ              ≈⟨ +ᶜ-comm _ _ ⟩
     (⌜ mo ⌝ · p) ·ᶜ δ +ᶜ γ              ≈˘⟨ +ᶜ-congˡ (*>-identityˡ _) ⟩
     (⌜ mo ⌝ · p) ·ᶜ δ +ᶜ idSubstₘ *> γ  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- A variant of sgSubstₘ-lemma₁.

sgSubstₘ-lemma₂ :
  γ ∙ ⌜ mo ⌝ · p ▸[ mo ] t → δ ▸[ mo ᵐ· p ] u →
  γ +ᶜ p ·ᶜ δ ▸[ mo ] t [ u ]
sgSubstₘ-lemma₂ {γ = γ} {mo = 𝟙ᵐ} {p = p} {δ = δ} γ▸t δ▸u = sub
  (sgSubstₘ-lemma₁ γ▸t δ▸u)
  (begin
     γ +ᶜ p ·ᶜ δ        ≈˘⟨ +ᶜ-congˡ (·ᶜ-congʳ (·-identityˡ _)) ⟩
     γ +ᶜ (𝟙 · p) ·ᶜ δ  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
sgSubstₘ-lemma₂ {γ = γ} {mo = 𝟘ᵐ} {p = p} {δ = δ} γ▸t δ▸u = sub
  (sgSubstₘ-lemma₁ γ▸t δ▸u)
  (begin
     γ +ᶜ p ·ᶜ δ        ≤⟨ +ᶜ-monotoneʳ (·ᶜ-monotoneʳ (▸-𝟘ᵐ δ▸u)) ⟩
     γ +ᶜ p ·ᶜ 𝟘ᶜ       ≈⟨ +ᶜ-congˡ (·ᶜ-zeroʳ _) ⟩
     γ +ᶜ 𝟘ᶜ            ≈˘⟨ +ᶜ-congˡ (·ᶜ-zeroˡ _) ⟩
     γ +ᶜ 𝟘 ·ᶜ δ        ≈˘⟨ +ᶜ-congˡ (·ᶜ-congʳ (·-zeroˡ _)) ⟩
     γ +ᶜ (𝟘 · p) ·ᶜ δ  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- Another variant of sgSubstₘ-lemma₁.

sgSubstₘ-lemma₃ :
  γ ∙ ⌜ mo ⌝ · p ▸[ mo ] t → δ ▸[ mo ] u →
  γ +ᶜ p ·ᶜ δ ▸[ mo ] t [ u ]
sgSubstₘ-lemma₃ {mo = 𝟘ᵐ} =
  sgSubstₘ-lemma₂
sgSubstₘ-lemma₃ {mo = 𝟙ᵐ} ▸t ▸u =
  case ▸[𝟙ᵐ]→▸[⌞⌟] ▸u of λ where
    (_ , ▸u , eq) → sub
      (sgSubstₘ-lemma₂ ▸t ▸u)
      (≤ᶜ-reflexive (+ᶜ-congˡ eq))

-- A substitution lemma for double substitutions.

doubleSubstₘ-lemma₁ :
  γ ∙ ⌜ mo ⌝ · q ∙ ⌜ mo ⌝ · p ▸[ mo ] t →
  δ ▸[ mo ᵐ· p ] u → η ▸[ mo ᵐ· q ] u′ →
  γ +ᶜ (⌜ mo ⌝ · p) ·ᶜ δ +ᶜ (⌜ mo ⌝ · q) ·ᶜ η ▸[ mo ] t [ u′ ,, u ]
doubleSubstₘ-lemma₁
  {γ = γ} {mo = mo} {q = q} {p = p} {δ = δ} {η = η} γ▸t δ▸u η▸u′ = sub
  (substₘ-lemma (consSubstₘ (sgSubstₘ _) _)
     (▶-cong (consSubstₘ (sgSubstₘ _) _)
        (λ where
           x0          → PE.sym (⌞⌜⌝·⌟ mo)
           (x0 +1)     → PE.sym (⌞⌜⌝·⌟ mo)
           ((_ +1) +1) → PE.refl)
        (wf-consSubstₘ (wf-sgSubstₘ (▸-·′ η▸u′)) (▸-·′ δ▸u)))
     γ▸t)
  (begin
     γ +ᶜ (⌜ mo ⌝ · p) ·ᶜ δ +ᶜ (⌜ mo ⌝ · q) ·ᶜ η              ≈⟨ +ᶜ-comm _ _ ⟩
     ((⌜ mo ⌝ · p) ·ᶜ δ +ᶜ (⌜ mo ⌝ · q) ·ᶜ η) +ᶜ γ            ≈⟨ +ᶜ-assoc _ _ _ ⟩
     (⌜ mo ⌝ · p) ·ᶜ δ +ᶜ (⌜ mo ⌝ · q) ·ᶜ η +ᶜ γ              ≈˘⟨ +ᶜ-congˡ (+ᶜ-congˡ (*>-identityˡ _)) ⟩
     (⌜ mo ⌝ · p) ·ᶜ δ +ᶜ (⌜ mo ⌝ · q) ·ᶜ η +ᶜ idSubstₘ *> γ  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- A variant of doubleSubstₘ-lemma₁.

doubleSubstₘ-lemma₂ :
  γ ∙ ⌜ mo ⌝ · q ∙ ⌜ mo ⌝ · p ▸[ mo ] t →
  δ ▸[ mo ᵐ· p ] u → η ▸[ mo ᵐ· q ] u′ →
  γ +ᶜ p ·ᶜ δ +ᶜ q ·ᶜ η ▸[ mo ] t [ u′ ,, u ]
doubleSubstₘ-lemma₂
  {γ = γ} {mo = 𝟙ᵐ} {q = q} {p = p} {δ = δ} {η = η} γ▸t δ▸u η▸u′ = sub
  (doubleSubstₘ-lemma₁ γ▸t δ▸u η▸u′)
  (begin
     γ +ᶜ p ·ᶜ δ +ᶜ q ·ᶜ η              ≈˘⟨ +ᶜ-congˡ (+ᶜ-cong (·ᶜ-congʳ (·-identityˡ _)) (·ᶜ-congʳ (·-identityˡ _))) ⟩
     γ +ᶜ (𝟙 · p) ·ᶜ δ +ᶜ (𝟙 · q) ·ᶜ η  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
doubleSubstₘ-lemma₂
  {γ = γ} {mo = 𝟘ᵐ} {q = q} {p = p} {δ = δ} {η = η} γ▸t δ▸u η▸u′ = sub
  (doubleSubstₘ-lemma₁ γ▸t δ▸u η▸u′)
  (begin
     γ +ᶜ p ·ᶜ δ +ᶜ q ·ᶜ η              ≤⟨ +ᶜ-monotoneʳ (+ᶜ-monotone (·ᶜ-monotoneʳ (▸-𝟘ᵐ δ▸u)) (·ᶜ-monotoneʳ (▸-𝟘ᵐ η▸u′))) ⟩
     γ +ᶜ p ·ᶜ 𝟘ᶜ +ᶜ q ·ᶜ 𝟘ᶜ            ≈⟨ +ᶜ-congˡ (+ᶜ-cong (·ᶜ-zeroʳ _) (·ᶜ-zeroʳ _)) ⟩
     γ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ                      ≈˘⟨ +ᶜ-congˡ (+ᶜ-cong (·ᶜ-zeroˡ _) (·ᶜ-zeroˡ _)) ⟩
     γ +ᶜ 𝟘 ·ᶜ δ +ᶜ 𝟘 ·ᶜ η              ≈˘⟨ +ᶜ-congˡ (+ᶜ-cong (·ᶜ-congʳ (·-zeroˡ _)) (·ᶜ-congʳ (·-zeroˡ _))) ⟩
     γ +ᶜ (𝟘 · p) ·ᶜ δ +ᶜ (𝟘 · q) ·ᶜ η  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- Another variant of doubleSubstₘ-lemma₁.

doubleSubstₘ-lemma₃ :
  γ ∙ ⌜ mo ⌝ · q ∙ ⌜ mo ⌝ · p ▸[ mo ] t →
  δ ▸[ mo ] u → η ▸[ mo ] u′ →
  γ +ᶜ p ·ᶜ δ +ᶜ q ·ᶜ η ▸[ mo ] t [ u′ ,, u ]
doubleSubstₘ-lemma₃ {mo = 𝟘ᵐ} =
  doubleSubstₘ-lemma₂
doubleSubstₘ-lemma₃ {mo = 𝟙ᵐ} ▸t ▸u ▸u′ =
  case ▸[𝟙ᵐ]→▸[⌞⌟] ▸u of λ where
    (_ , ▸u , eq) → case ▸[𝟙ᵐ]→▸[⌞⌟] ▸u′ of λ where
      (_ , ▸u′ , eq′) → sub
        (doubleSubstₘ-lemma₂ ▸t ▸u ▸u′)
        (≤ᶜ-reflexive (+ᶜ-congˡ (+ᶜ-cong eq eq′)))

-------------------------------------
-- Substitution matrix inference --
-------------------------------------

-- The inference functions ∥_∥ and ⌈_⌉ are related to each other: the
-- x-th column of ∥ σ ∥ mos is equivalent to ⌈ σ x ⌉ (mos x).

substₘ-calc-col :
  (σ : Subst m n) (x : Fin n) →
  ∥ σ ∥ mos *> (𝟘ᶜ , x ≔ 𝟙) ≈ᶜ ⌈ σ x ⌉ (mos x)
substₘ-calc-col {mos = mos} σ x0 = begin
  ∥ σ ∥ mos *> (𝟘ᶜ , x0 ≔ 𝟙)                                 ≡⟨⟩
  ∥ σ ∥ mos *> (𝟘ᶜ ∙ 𝟙)                                      ≡⟨⟩
  𝟙 ·ᶜ ⌈ σ x0 ⌉ (headᵐ mos) +ᶜ ∥ tail σ ∥ (tailᵐ mos) *> 𝟘ᶜ  ≈⟨ +ᶜ-cong (·ᶜ-identityˡ _) (*>-zeroʳ (∥ tail σ ∥ _)) ⟩
  ⌈ σ x0 ⌉ (headᵐ mos) +ᶜ 𝟘ᶜ                                 ≈⟨ +ᶜ-identityʳ _ ⟩
  ⌈ σ x0 ⌉ (headᵐ mos)                                       ∎
  where open Tools.Reasoning.Equivalence Conₘ-setoid
substₘ-calc-col {mos = mos} σ (x +1) = begin
  ∥ σ ∥ mos *> (𝟘ᶜ , x +1 ≔ 𝟙)                                         ≡⟨⟩
  ∥ σ ∥ mos *> ((𝟘ᶜ , x ≔ 𝟙) ∙ 𝟘)                                      ≡⟨⟩
  𝟘 ·ᶜ ⌈ σ x0 ⌉ (headᵐ mos) +ᶜ ∥ tail σ ∥ (tailᵐ mos) *> (𝟘ᶜ , x ≔ 𝟙)  ≈⟨ +ᶜ-cong (·ᶜ-zeroˡ _) (substₘ-calc-col (tail σ) x) ⟩
  𝟘ᶜ +ᶜ ⌈ tail σ x ⌉ (tailᵐ mos x)                                     ≈⟨ +ᶜ-identityˡ _ ⟩
  ⌈ σ (x +1) ⌉ (tailᵐ mos x)                                           ∎
  where open Tools.Reasoning.Equivalence Conₘ-setoid


-- An inferred substitution matrix is well-formed if all substituted
-- terms are well-resourced (for suitable modes).

substₘ-calc-correct :
  {Γ : Con Term m} (σ : Subst m n) →
  (∀ x → ∃ λ γ → γ ▸[ mos x ] σ x) → ∥ σ ∥ mos ▶[ mos ] σ
substₘ-calc-correct {mos = mos} σ prop x with prop x
... | γ , γ▸σx = sub
  (usage-inf γ▸σx)
  (begin
     ∥ σ ∥ mos *> (𝟘ᶜ , x ≔ ⌜ mos x ⌝)       ≈˘⟨ ·ᶜ-*>-𝟘ᶜ,≔𝟙 (∥ σ ∥ _) ⟩
     ⌜ mos x ⌝ ·ᶜ ∥ σ ∥ mos *> (𝟘ᶜ , x ≔ 𝟙)  ≈⟨ ·ᶜ-congˡ (substₘ-calc-col σ _) ⟩
     ⌜ mos x ⌝ ·ᶜ ⌈ σ x ⌉ (mos x)            ≈⟨ ·-⌈⌉ {m = mos x} (σ x) ⟩
     ⌈ σ x ⌉ (mos x)                         ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

subst-calc-correct′ :
  (Ψ : Substₘ m n) →
  Ψ ▶[ mos ] σ → ∥ σ ∥ mos ▶[ mos ] σ
subst-calc-correct′ {mos = mos} {σ = σ} (Ψ ⊙ γ) Ψ▶σ x0 = sub
  (usage-inf (Ψ▶σ x0))
  (begin
     ⌜ headᵐ mos ⌝ ·ᶜ ⌈ head σ ⌉ (headᵐ mos) +ᶜ
     ∥ tail σ ∥ (tailᵐ mos) *> 𝟘ᶜ                   ≈⟨ +ᶜ-congˡ (*>-zeroʳ (∥ tail σ ∥ _)) ⟩

     ⌜ headᵐ mos ⌝ ·ᶜ ⌈ head σ ⌉ (headᵐ mos) +ᶜ 𝟘ᶜ  ≈⟨ +ᶜ-identityʳ _ ⟩

     ⌜ headᵐ mos ⌝ ·ᶜ ⌈ head σ ⌉ (headᵐ mos)        ≈⟨ ·-⌈⌉ (head σ) ⟩

     ⌈ head σ ⌉ (headᵐ mos)                         ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
subst-calc-correct′ (Ψ ⊙ γ) Ψ▶σ (x +1) =
  sub (subst-calc-correct′ Ψ (wf-tailSubstₘ Ψ▶σ) x)
      (≤ᶜ-reflexive (≈ᶜ-trans (+ᶜ-congʳ (·ᶜ-zeroˡ _)) (+ᶜ-identityˡ _)))

-- Each column of a calculated substitution matrix is an upper bound
-- of the usage contexts (for a suitable mode) of the corresponding
-- substituted term.

substₘ-calc-upper-bound :
  {γ : Conₘ m} (σ : Subst m n) (x : Fin n) →
  γ ▸[ mos x ] σ x → γ ≤ᶜ ∥ σ ∥ mos *> (𝟘ᶜ , x ≔ 𝟙)
substₘ-calc-upper-bound σ x γ▸σx =
  ≤ᶜ-trans (usage-upper-bound γ▸σx)
           (≤ᶜ-reflexive (≈ᶜ-sym (substₘ-calc-col σ x)))

--------------------------------------------------
-- Well-formedness of substitution compositions --
--------------------------------------------------

-- Compositions of suitably well-formed substitutions are well-formed.

wf-compSubst :
  (Ψ : Substₘ m ℓ) {Φ : Substₘ ℓ n} {σ : Subst m ℓ} {σ′ : Subst ℓ n} →
  Ψ ▶[ ⌞ Φ *> ⌜ mos ⌝ᶜ ⌟ᶜ ] σ → Φ ▶[ mos ] σ′ →
  (Ψ <*> Φ) ▶[ mos ] (σ ₛ•ₛ σ′)
wf-compSubst {mos = mos} Ψ {Φ = Φ} {σ = σ} {σ′ = σ′} Ψ▶σ Φ▶σ′ x = sub
  (substₘ-lemma Ψ
     (▶-cong Ψ
        (λ y → cong (λ p → ⌞ Φ *> (_ , _ ≔ p) ⌟ᶜ _) (⌜⌝ᶜ⟨⟩ x))
        (▶-⌞*>⌟ Ψ {Φ = Φ} Ψ▶σ))
     (Φ▶σ′ x))
  (begin
     (Ψ <*> Φ) *> (𝟘ᶜ , x ≔ ⌜ mos x ⌝)       ≈˘⟨ ·ᶜ-*>-𝟘ᶜ,≔𝟙 (Ψ <*> Φ) ⟩
     ⌜ mos x ⌝ ·ᶜ (Ψ <*> Φ) *> (𝟘ᶜ , x ≔ 𝟙)  ≈⟨ ·ᶜ-congˡ (<*>-*>-assoc Ψ Φ _) ⟩
     ⌜ mos x ⌝ ·ᶜ Ψ *> (Φ *> (𝟘ᶜ , x ≔ 𝟙))   ≈˘⟨ *>-distrib-·ᶜ Ψ _ _ ⟩
     Ψ *> (⌜ mos x ⌝ ·ᶜ Φ *> (𝟘ᶜ , x ≔ 𝟙))   ≈⟨ *>-cong Ψ (·ᶜ-*>-𝟘ᶜ,≔𝟙 Φ) ⟩
     Ψ *> (Φ *> (𝟘ᶜ , x ≔ ⌜ mos x ⌝))        ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
