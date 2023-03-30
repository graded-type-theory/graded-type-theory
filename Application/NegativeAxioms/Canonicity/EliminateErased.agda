-- Proof that consistent negative axioms do not jeopardize canonicity.
-- https://www.cs.bham.ac.uk/~mhe/papers/negative-axioms.pdf

open import Tools.Bool

module Application.NegativeAxioms.Canonicity.EliminateErased
  -- Is 𝟘ᵐ allowed?
  (𝟘ᵐ-allowed : Bool)
  where

open import Definition.Modality.Instances.Erasure

open import Definition.Modality.Restrictions Erasure

open import Definition.Modality.Instances.Erasure.Modality
  (𝟘ᵐ-allowed-if 𝟘ᵐ-allowed)
open import Application.NegativeAxioms.NegativeErasedContext ErasureModality (λ ())
  hiding (lookupNegative)
open import Definition.Typed Erasure
open import Definition.Untyped Erasure hiding (_∷_; ℕ≢B)

open import Definition.Modality.Context ErasureModality
open import Definition.Modality.Context.Properties ErasureModality
open import Definition.Modality.Properties ErasureModality
open import Definition.Modality.Usage ErasureModality
open import Definition.Mode ErasureModality

open import Erasure.SucRed Erasure

open import Definition.Typed.Properties Erasure
open import Definition.Typed.Consequences.Canonicity Erasure
open import Definition.Typed.Consequences.Substitution Erasure

open import Definition.Conversion Erasure
open import Definition.Conversion.Consequences.Completeness Erasure

open import Tools.Empty
open import Tools.Fin
open import Tools.Nat
open import Tools.Nullary
import Tools.PropositionalEquality as PE
open import Tools.Product

private
  module EM = Modality ErasureModality

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

lem :
  ε ∙ (Σᵣ ω , 𝟘 ▷ ℕ ▹ ℕ) ⊢
    prodrec 𝟘 ω 𝟘 ℕ (var x0) zero [conv↑] zero ∷ ℕ →
  ⊥
lem ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u)
  with whnfRed*Term d (ne (prodrecₙ (var x0)))
     | whnfRed*Term d′ zeroₙ
     | whnfRed* D ℕₙ
lem ([↑]ₜ _ _ _ D d d′ whnfB whnft′ whnfu′ (ℕ-ins ()))
  | PE.refl | PE.refl | PE.refl
lem ([↑]ₜ _ _ _ D d d′ whnfB whnft′ whnfu′ (ne-ins x x₁ x₂ ()))
  | PE.refl | PE.refl | PE.refl

lem′ :
  ε ∙ (Σᵣ ω , 𝟘 ▷ ℕ ▹ ℕ) ⊢
    prodrec 𝟘 ω 𝟘 ℕ (var x0) zero [conv↑] suc t ∷ ℕ →
  ⊥
lem′ ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u)
  with whnfRed*Term d (ne (prodrecₙ (var x0)))
     | whnfRed*Term d′ sucₙ
     | whnfRed* D ℕₙ
lem′ ([↑]ₜ _ _ _ D d d′ whnfB whnft′ whnfu′ (ℕ-ins ()))
  | PE.refl | PE.refl | PE.refl
lem′ ([↑]ₜ _ _ _ D d d′ whnfB whnft′ whnfu′ (ne-ins x x₁ x₂ ()))
  | PE.refl | PE.refl | PE.refl

-- Counterexample to canonicity when erased eliminations are allowed

cEx : ∃₄ λ (m : Nat) (Γ : Con Term m) (γ : Conₘ m) (t : Term m)
    → Γ ⊢ t ∷ ℕ
    × γ ▸[ 𝟙ᵐ ] t
    × γ PE.≡ 𝟘ᶜ
    × NegativeErasedContext Γ γ
    × (∀ {u} → Γ ⊢ u ∷ Empty → ⊥)
    × ((∃ λ u → Numeral u × Γ ⊢ t ≡ u ∷ ℕ) → ⊥)
    × ((∃ λ u → Numeral u × Γ ⊢ t ⇒ˢ* u ∷ℕ) → ⊥)
    × (∃ λ u → Γ ⊢ t ⇒* u ∷ ℕ × Whnf u × Neutral u)
cEx = _ , ε ∙ (Σᵣ ω , 𝟘 ▷ ℕ ▹ ℕ) , _ , prodrec 𝟘 ω 𝟘 ℕ (var x0) zero
    , ⊢prodrec
    , prodrecₘ {η = 𝟘ᶜ} var zeroₘ
        (sub ℕₘ (≤ᶜ-refl ∙ ≤-reflexive (EM.·-zeroʳ _))) _
    , PE.refl
    , ε ∙𝟘
    , (λ ⊢t → ¬Empty (substTerm ⊢t (prodⱼ ε⊢ℕ εℕ⊢ℕ (zeroⱼ ε) (zeroⱼ ε))))
    , (λ { (.zero , zeroₙ , t≡u) → lem (completeEqTerm t≡u)
         ; (.(suc _) , sucₙ numU , t≡u) → lem′ (completeEqTerm t≡u)
         })
    , (λ { (u , numU , (whred x ⇨ˢ d)) → neRedTerm x (prodrecₙ (var x0))})
    , (_ , id ⊢prodrec , ne neutral , neutral)
    where
    ε⊢ℕ = ℕⱼ ε
    ⊢εℕ = ε ∙ ε⊢ℕ
    εℕ⊢ℕ = ℕⱼ ⊢εℕ
    ε⊢Σ = ΠΣⱼ ε⊢ℕ ▹ εℕ⊢ℕ
    ⊢εΣ = ε ∙ ε⊢Σ
    εΣ⊢ℕ = ℕⱼ ⊢εΣ
    ⊢εΣℕ = ⊢εΣ ∙ εΣ⊢ℕ
    εΣℕ⊢ℕ = ℕⱼ ⊢εΣℕ
    εΣ⊢Σ = ΠΣⱼ εΣ⊢ℕ ▹ εΣℕ⊢ℕ
    ⊢εΣΣ = ⊢εΣ ∙ εΣ⊢Σ
    εΣΣ⊢ℕ = ℕⱼ ⊢εΣΣ
    ⊢εΣℕℕ = ⊢εΣℕ ∙ εΣℕ⊢ℕ
    ⊢prodrec =
      prodrecⱼ {r = 𝟘} εΣ⊢ℕ εΣℕ⊢ℕ εΣΣ⊢ℕ (var ⊢εΣ here) (zeroⱼ ⊢εΣℕℕ)
    neutral = prodrecₙ (var _)

-- If one drops the restriction related to prodrec from the statement
-- of
-- Application.NegativeAxioms.Canonicity.NegativeErased.canonicityEq,
-- then the lemma cannot be proved (assuming that Agda is consistent).

not-canonicityEq :
  ¬ (∀ {n} {Γ : Con Term n} {t γ} →
     NegativeErasedContext Γ γ →
     (∀ {t} → Γ ⊢ t ∷ Empty → ⊥) →
     Γ ⊢ t ∷ ℕ → γ ▸[ 𝟙ᵐ ] t →
     ∃ λ u → Numeral u × Γ ⊢ t ≡ u ∷ ℕ)
not-canonicityEq hyp =
  let _ , _ , _ , _ , ⊢t , ▸t , _ , nec , con , not-numeral , _ = cEx in
  not-numeral (hyp nec con ⊢t ▸t)
