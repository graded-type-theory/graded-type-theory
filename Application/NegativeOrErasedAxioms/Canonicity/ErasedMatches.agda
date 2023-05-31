------------------------------------------------------------------------
-- If erased matches are not allowed. Erased axioms do jeopardize
-- canonicity.
------------------------------------------------------------------------

open import Graded.Mode.Restrictions

module Application.NegativeOrErasedAxioms.Canonicity.ErasedMatches
  (mrs : Mode-restrictions)
  where

open import Graded.Modality.Instances.Erasure
open import Graded.Modality.Instances.Erasure.Modality mrs
open import Application.NegativeOrErasedAxioms.NegativeOrErasedContext
  ErasureModality (λ ())
import Definition.Typed
open import Definition.Untyped Erasure hiding (_∷_)

open import Graded.Context ErasureModality
open import Graded.Context.Properties ErasureModality
open import Graded.Modality.Properties ErasureModality
open import Graded.Restrictions {M = Erasure}
import Graded.Usage
open import Graded.Usage.Restrictions Erasure
open import Graded.Mode ErasureModality

import Graded.Erasure.SucRed

import Definition.Typed.Properties
open import Definition.Typed.Restrictions Erasure
import Definition.Typed.Consequences.Canonicity
import Definition.Typed.Consequences.Substitution

import Definition.Conversion
import Definition.Conversion.Consequences.Completeness

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Nullary
import Tools.PropositionalEquality as PE
open import Tools.Product

private
  module EM = Modality ErasureModality

private variable
  m : Nat
  t : Term m

module Counterexample where

  open Definition.Conversion no-type-restrictions
  open Definition.Conversion.Consequences.Completeness
    no-type-restrictions
  open Graded.Usage ErasureModality no-usage-restrictions
  open Definition.Typed no-type-restrictions
  open Definition.Typed.Consequences.Canonicity no-type-restrictions
  open Definition.Typed.Consequences.Substitution no-type-restrictions
  open Definition.Typed.Properties no-type-restrictions
  open Graded.Erasure.SucRed no-type-restrictions

  -- A counterexample to canonicity. Note that the use of
  -- no-usage-restrictions above means that erased eliminations are
  -- allowed.

  cEx :
    ∃₄ λ (m : Nat) (Γ : Con Term m) (γ : Conₘ m) (t : Term m)
    → Γ ⊢ t ∷ ℕ
    × γ ▸[ 𝟙ᵐ ] t
    × γ PE.≡ 𝟘ᶜ
    × NegativeErasedContext no-type-restrictions Γ γ
    × (∀ {u} → Γ ⊢ u ∷ Empty → ⊥)
    × ((∃ λ u → Numeral u × Γ ⊢ t ≡ u ∷ ℕ) → ⊥)
    × ((∃ λ u → Numeral u × Γ ⊢ t ⇒ˢ* u ∷ℕ) → ⊥)
    × (∃ λ u → Γ ⊢ t ⇒* u ∷ ℕ × Whnf u × Neutral u)
  cEx =
      _
    , ε ∙ (Σᵣ ω , 𝟘 ▷ ℕ ▹ ℕ) , _ , prodrec 𝟘 ω 𝟘 ℕ (var x0) zero
    , ⊢prodrec
    , prodrecₘ {η = 𝟘ᶜ} var zeroₘ
        (sub ℕₘ (≤ᶜ-refl ∙ ≤-reflexive (EM.·-zeroʳ _))) _
    , PE.refl
    , ε ∙𝟘
    , (λ ⊢t → ¬Empty $
              substTerm ⊢t (prodⱼ ε⊢ℕ εℕ⊢ℕ (zeroⱼ ε) (zeroⱼ ε) _))
    , (λ { (.zero , zeroₙ , t≡u) → lem (completeEqTerm t≡u)
         ; (.(suc _) , sucₙ numU , t≡u) → lem′ (completeEqTerm t≡u)
         })
    , (λ { (u , numU , (whred x ⇨ˢ d)) → neRedTerm x (prodrecₙ (var x0))})
    , (_ , id ⊢prodrec , ne neutral , neutral)
    where
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

    ε⊢ℕ = ℕⱼ ε
    ⊢εℕ = ε ∙ ε⊢ℕ
    εℕ⊢ℕ = ℕⱼ ⊢εℕ
    ε⊢Σ = ΠΣⱼ ε⊢ℕ εℕ⊢ℕ _
    ⊢εΣ = ε ∙ ε⊢Σ
    εΣ⊢ℕ = ℕⱼ ⊢εΣ
    ⊢εΣℕ = ⊢εΣ ∙ εΣ⊢ℕ
    εΣℕ⊢ℕ = ℕⱼ ⊢εΣℕ
    εΣ⊢Σ = ΠΣⱼ εΣ⊢ℕ εΣℕ⊢ℕ _
    ⊢εΣΣ = ⊢εΣ ∙ εΣ⊢Σ
    εΣΣ⊢ℕ = ℕⱼ ⊢εΣΣ
    ⊢εΣℕℕ = ⊢εΣℕ ∙ εΣℕ⊢ℕ
    ⊢prodrec =
      prodrecⱼ {r = 𝟘} εΣ⊢ℕ εΣℕ⊢ℕ εΣΣ⊢ℕ (var ⊢εΣ here) (zeroⱼ ⊢εΣℕℕ)
        _
    neutral = prodrecₙ (var _)

-- If one drops the assumption about erased matches from the statement
-- of
-- Application.NegativeAxioms.Canonicity.NegativeErased.canonicityEq,
-- then the lemma cannot be proved (assuming that Agda is consistent).

not-canonicityEq :
  ¬ ((TR : Type-restrictions) →
     let open Definition.Typed TR in
     (UR : Usage-restrictions) →
     let open Graded.Usage ErasureModality UR in
     ∀ {n} {Γ : Con Term n} {γ} →
     NegativeErasedContext TR Γ γ →
     (∀ {t} → Γ ⊢ t ∷ Empty → ⊥) →
     ∀ {t} → Γ ⊢ t ∷ ℕ → γ ▸[ 𝟙ᵐ ] t →
     ∃ λ u → Numeral u × Γ ⊢ t ≡ u ∷ ℕ)
not-canonicityEq hyp =
  case Counterexample.cEx of λ {
    (_ , _ , _ , _ , ⊢t , ▸t , _ , nec , con , not-numeral , _) →
  not-numeral
    (hyp no-type-restrictions no-usage-restrictions nec con ⊢t ▸t) }
