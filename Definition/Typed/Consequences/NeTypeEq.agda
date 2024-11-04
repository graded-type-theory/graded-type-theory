------------------------------------------------------------------------
-- Neutral terms have only one type (up to type equality).
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Consequences.NeTypeEq
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M
open import Definition.Typed R
open import Definition.Typed.Consequences.Syntactic R
open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.Consequences.Substitution R
open import Definition.Typed.Properties R

open import Graded.Derived.Erased.Typed R

open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n

-- Helper function for the same variable instance of a context have equal types.
varTypeEq′ : ∀ {n R T} → n ∷ R ∈ Γ → n ∷ T ∈ Γ → R PE.≡ T
varTypeEq′ here here = PE.refl
varTypeEq′ (there n∷R) (there n∷T) rewrite varTypeEq′ n∷R n∷T = PE.refl

-- The same variable instance of a context have equal types.
varTypeEq : ∀ {x A B} → Γ ⊢ A → Γ ⊢ B → x ∷ A ∈ Γ → x ∷ B ∈ Γ → Γ ⊢ A ≡ B
varTypeEq A B x∷A x∷B rewrite varTypeEq′ x∷A x∷B = refl A

-- The same neutral term have equal types.
neTypeEq : ∀ {t A B} → Neutral t → Γ ⊢ t ∷ A → Γ ⊢ t ∷ B → Γ ⊢ A ≡ B
neTypeEq (var x) (var x₁ x₂) (var x₃ x₄) =
  varTypeEq (syntacticTerm (var x₃ x₂)) (syntacticTerm (var x₃ x₄)) x₂ x₄
neTypeEq (∘ₙ neT) (t∷A ∘ⱼ t∷A₁) (t∷B ∘ⱼ t∷B₁) with neTypeEq neT t∷A t∷B
... | q = let w = proj₁ (proj₂ (injectivity q))
          in  substTypeEq w (refl t∷A₁)
neTypeEq (fstₙ neP) (fstⱼ _ ⊢t) (fstⱼ _ ⊢t′) with neTypeEq neP ⊢t ⊢t′
... | q = proj₁ (Σ-injectivity q)
neTypeEq (sndₙ neP) (sndⱼ ⊢G ⊢t) (sndⱼ _ ⊢t′) with neTypeEq neP ⊢t ⊢t′
... | q = let G≡G₁ = proj₁ (proj₂ (Σ-injectivity q))
              ⊢fst = fstⱼ ⊢G ⊢t
          in  substTypeEq G≡G₁ (refl ⊢fst)
neTypeEq (natrecₙ _) ⊢t@(natrecⱼ _ _ _) (natrecⱼ _ _ _) =
  refl (syntacticTerm ⊢t)
neTypeEq
  (prodrecₙ neT) (prodrecⱼ ⊢A ⊢t _ _) (prodrecⱼ _ _ _ _) =
  refl (substType ⊢A ⊢t)
neTypeEq (emptyrecₙ neT) (emptyrecⱼ x t∷A) (emptyrecⱼ x₁ t∷B) =
  refl x₁
neTypeEq (unitrecₙ _ neT) (unitrecⱼ ⊢A ⊢t _ _) (unitrecⱼ _ _ _ _) =
  refl (substType ⊢A ⊢t)
neTypeEq {Γ} (Jₙ _) (Jⱼ {w} _ ⊢B _ ⊢v ⊢w) (Jⱼ _ _ _ _ _) =
  refl $
  substType₂ ⊢B ⊢v $
  PE.subst (Γ ⊢ w ∷_) ≡Id-wk1-wk1-0[]₀ ⊢w
neTypeEq (Kₙ _) (Kⱼ _ ⊢B _ ⊢v _) (Kⱼ _ _ _ _ _) =
  refl (substType ⊢B ⊢v)
neTypeEq ([]-congₙ _) ([]-congⱼ _ ⊢t ⊢u _ ok) ([]-congⱼ _ _ _ _ _) =
  refl (Idⱼ′ ([]ⱼ ([]-cong→Erased ok) ⊢t) ([]ⱼ ([]-cong→Erased ok) ⊢u))
neTypeEq x (conv t∷A x₁) t∷B = let q = neTypeEq x t∷A t∷B
                               in  trans (sym x₁) q
neTypeEq x t∷A (conv t∷B x₃) = let q = neTypeEq x t∷A t∷B
                               in  trans q x₃
