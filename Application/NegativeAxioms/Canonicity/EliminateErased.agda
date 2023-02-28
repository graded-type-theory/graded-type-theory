-- Proof that consistent negative axioms do not jeopardize canonicity.
-- https://www.cs.bham.ac.uk/~mhe/papers/negative-axioms.pdf

{-# OPTIONS --without-K --safe #-}

open import Definition.Modality.Instances.Erasure
open import Definition.Modality.Instances.Erasure.Modality (_≤ 𝟘)
open import Application.NegativeAxioms.NegativeErasedContext ErasureModality (λ ())
  hiding (lookupNegative)
open import Definition.Typed Erasure′
open import Definition.Untyped Erasure hiding (_∷_; ℕ≢B)


open import Tools.Empty

module Application.NegativeAxioms.Canonicity.EliminateErased where

open import Definition.Modality.Instances.Erasure.Properties (_≤ ω)
open import Definition.Modality.Context ErasureModality
open import Definition.Modality.Usage ErasureModality
open import Definition.Modality.Usage.Inversion ErasureModality
open import Definition.Modality.FullReduction ErasureModality greatest-elem

open import Application.NegativeAxioms.NegativeType Erasure′
open import Erasure.SucRed Erasure′

open import Definition.Typed.Properties Erasure′
open import Definition.Typed.Usage ErasureModality
open import Definition.Typed.Consequences.Canonicity Erasure′
open import Definition.Typed.Consequences.Consistency Erasure′
open import Definition.Typed.Consequences.Inequality Erasure′
open import Definition.Typed.Consequences.Injectivity Erasure′
open import Definition.Typed.Consequences.Inversion Erasure′
open import Definition.Typed.Consequences.Reduction Erasure′
open import Definition.Typed.Consequences.Substitution Erasure′
open import Definition.Typed.Consequences.Syntactic Erasure′

open import Tools.Fin
open import Tools.Nat
import Tools.PropositionalEquality as PE
open import Tools.Product
open import Tools.Sum using (_⊎_; inj₁; inj₂)


-- Preliminaries
---------------------------------------------------------------------------

private
  Ty  = Term
  Cxt = Con Ty
  variable
    m  : Nat
    Γ   : Con Term m
    A B C : Term m
    t u   : Term m
    p q   : Erasure

-- Counterexample to canonicity when erased eliminations are allowed

cEx : ∃₃ λ (m : Nat) (Γ : Con Term m) (t : Term m)
    → Γ ⊢ t ∷ ℕ
    × 𝟘ᶜ ▸ t
    × (∀ {u} → Γ ⊢ u ∷ Empty → ⊥)
    × ((∃ λ u → Numeral u × Γ ⊢ t ⇒ˢ* u ∷ℕ) → ⊥)
cEx = _ , ε ∙ (Σᵣ 𝟘 ▷ ℕ ▹ ℕ) , prodrec 𝟘 𝟘 ℕ (var x0) zero
    , prodrecⱼ εΣ⊢ℕ εΣℕ⊢ℕ εΣΣ⊢ℕ (var ⊢εΣ here) (zeroⱼ ⊢εΣℕℕ)
    , prodrecₘ var zeroₘ ℕₘ PE.refl
    , (λ ⊢t → ¬Empty (substTerm ⊢t (prodⱼ ε⊢ℕ εℕ⊢ℕ (zeroⱼ ε) (zeroⱼ ε))))
    , λ { (u , numU , (whred x ⇨ˢ d)) → neRedTerm x (prodrecₙ (var x0))}
    where
    ε⊢ℕ = ℕⱼ ε
    ⊢εℕ = ε ∙ ε⊢ℕ
    εℕ⊢ℕ = ℕⱼ ⊢εℕ
    ε⊢Σ = Σⱼ ε⊢ℕ ▹ εℕ⊢ℕ
    ⊢εΣ = ε ∙ ε⊢Σ
    εΣ⊢ℕ = ℕⱼ ⊢εΣ
    ⊢εΣℕ = ⊢εΣ ∙ εΣ⊢ℕ
    εΣℕ⊢ℕ = ℕⱼ ⊢εΣℕ
    εΣ⊢Σ = Σⱼ εΣ⊢ℕ ▹ εΣℕ⊢ℕ
    ⊢εΣΣ = ⊢εΣ ∙ εΣ⊢Σ
    εΣΣ⊢ℕ = ℕⱼ ⊢εΣΣ
    ⊢εΣℕℕ = ⊢εΣℕ ∙ εΣℕ⊢ℕ
