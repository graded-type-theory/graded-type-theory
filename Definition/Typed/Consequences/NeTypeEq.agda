------------------------------------------------------------------------
-- Neutral terms have only one type (up to type equality) if equality
-- reflection is not allowed
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
open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Substitution R
open import Definition.Typed.Syntactic R
open import Definition.Typed.Weakening R as W
open import Definition.Typed.Well-formed R

open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Sum

private
  variable
    m n   : Nat
    Δ     : Con Term n
    Γ     : Cons m n
    A B t : Term _
    V     : Set a

-- Helper function for the same variable instance of a context have equal types.
varTypeEq′ : ∀ {n R T} → n ∷ R ∈ Δ → n ∷ T ∈ Δ → R PE.≡ T
varTypeEq′ here here = PE.refl
varTypeEq′ (there n∷R) (there n∷T) rewrite varTypeEq′ n∷R n∷T = PE.refl

-- The same variable instance of a context have equal types.
varTypeEq :
  ∀ {x A B} →
  Γ ⊢ A → Γ ⊢ B → x ∷ A ∈ Γ .vars → x ∷ B ∈ Γ .vars → Γ ⊢ A ≡ B
varTypeEq A B x∷A x∷B rewrite varTypeEq′ x∷A x∷B = refl A

-- Types are unique for neutral terms (given a certain assumption).

neTypeEq :
  ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
  Neutral V (Γ .defs) t → Γ ⊢ t ∷ A → Γ ⊢ t ∷ B → Γ ⊢ A ≡ B
neTypeEq (defn α↦⊘) (defn ⊢Γ α↦∷A PE.refl) (defn _ α↦∷B PE.refl) =
  case unique-↦∈ α↦∷A α↦∷B PE.refl of λ where
    PE.refl → refl (W.wk (wk₀∷ʷ⊇ ⊢Γ) (wf-↦∈ α↦∷A (defn-wf ⊢Γ)))
neTypeEq (var ok x) (var x₁ x₂) (var x₃ x₄) =
  varTypeEq (syntacticTerm (var x₃ x₂)) (syntacticTerm (var x₃ x₄)) x₂ x₄
neTypeEq (supᵘˡₙ _) (supᵘⱼ ⊢t _) (supᵘⱼ _ _) =
  refl (wf-⊢∷ ⊢t)
neTypeEq (supᵘʳₙ _) (supᵘⱼ ⊢t _) (supᵘⱼ _ _) =
  refl (wf-⊢∷ ⊢t)
neTypeEq (lowerₙ x) (lowerⱼ y) (lowerⱼ z) = Lift-injectivity (neTypeEq x y z) .proj₂
neTypeEq (∘ₙ neT) (t∷A ∘ⱼ t∷A₁) (t∷B ∘ⱼ t∷B₁) with neTypeEq neT t∷A t∷B
... | q = ΠΣ-injectivity q .proj₂ .proj₁ (refl t∷A₁)
neTypeEq (fstₙ neP) (fstⱼ _ ⊢t) (fstⱼ _ ⊢t′) with neTypeEq neP ⊢t ⊢t′
... | q = proj₁ (ΠΣ-injectivity q)
neTypeEq (sndₙ neP) (sndⱼ ⊢G ⊢t) (sndⱼ _ ⊢t′) with neTypeEq neP ⊢t ⊢t′
... | q = ΠΣ-injectivity q .proj₂ .proj₁ (refl (fstⱼ ⊢G ⊢t))
neTypeEq (natrecₙ _) ⊢t@(natrecⱼ _ _ _) (natrecⱼ _ _ _) =
  refl (syntacticTerm ⊢t)
neTypeEq
  (prodrecₙ neT) (prodrecⱼ ⊢A ⊢t _ _) (prodrecⱼ _ _ _ _) =
  refl (substType ⊢A ⊢t)
neTypeEq (emptyrecₙ neT) (emptyrecⱼ x t∷A) (emptyrecⱼ x₁ t∷B) =
  refl x₁
neTypeEq (unitrecₙ _ neT) (unitrecⱼ ⊢A ⊢t _ _) (unitrecⱼ _ _ _ _) =
  refl (substType ⊢A ⊢t)
neTypeEq (Jₙ _) (Jⱼ {w} _ ⊢B _ ⊢v ⊢w) (Jⱼ _ _ _ _ _) =
  refl $
  subst-⊢₁₀ ⊢B ⊢v $
  PE.subst (_⊢_∷_ _ _) ≡Id-wk1-wk1-0[]₀ ⊢w
neTypeEq (Kₙ _) (Kⱼ ⊢B _ ⊢v _) (Kⱼ _ _ _ _) =
  refl (substType ⊢B ⊢v)
neTypeEq
  ([]-congₙ _) ([]-congⱼ ⊢l _ ⊢t ⊢u _ ok) ([]-congⱼ _ _ _ _ _ _) =
  refl $
  Idⱼ′ ([]ⱼ ([]-cong→Erased ok) ⊢l ⊢t) ([]ⱼ ([]-cong→Erased ok) ⊢l ⊢u)
neTypeEq x (conv t∷A x₁) t∷B = let q = neTypeEq x t∷A t∷B
                               in  trans (sym x₁) q
neTypeEq x t∷A (conv t∷B x₃) = let q = neTypeEq x t∷A t∷B
                               in  trans q x₃
