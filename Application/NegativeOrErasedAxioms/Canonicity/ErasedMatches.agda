------------------------------------------------------------------------
-- If erased matches are not allowed. Erased axioms do jeopardize
-- canonicity.
------------------------------------------------------------------------

module Application.NegativeOrErasedAxioms.Canonicity.ErasedMatches where

open import Tools.Bool
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Level
open import Tools.Nat using (Nat)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Sum using (_⊎_)

import Application.NegativeOrErasedAxioms.NegativeOrErasedContext

import Definition.Conversion
import Definition.Conversion.Consequences.Completeness
import Definition.Typed
import Definition.Typed.Consequences.Canonicity
import Definition.Typed.Consequences.Consistency
import Definition.Typed.Consequences.Substitution
import Definition.Typed.Properties
open import Definition.Typed.Restrictions
import Definition.Untyped
import Definition.Untyped.Neutral

import Graded.Context
import Graded.Context.Properties
import Graded.Erasure.SucRed
import Graded.Modality
import Graded.Modality.Properties
open import Graded.Modality.Variant lzero
import Graded.Mode
import Graded.Restrictions
import Graded.Usage
open import Graded.Usage.Restrictions

open import Graded.Modality.Instances.Erasure as E using (Erasure)
import Graded.Modality.Instances.Erasure.Modality as EM

module Counterexample
  (variant : Modality-variant)
  where

  open Graded.Modality Erasure

  private

    -- The modality used in this local module.

    𝕄 = EM.ErasureModality variant

    module M = Modality 𝕄

    open Graded.Restrictions 𝕄

    -- The type and usage restrictions used in this local module.

    TR : Type-restrictions 𝕄
    TR = no-type-restrictions true

    UR : Usage-restrictions 𝕄
    UR = no-usage-restrictions true true

  open Type-restrictions TR

  open Application.NegativeOrErasedAxioms.NegativeOrErasedContext TR

  open Definition.Conversion TR
  open Definition.Conversion.Consequences.Completeness TR
  open Definition.Typed TR
  open Definition.Typed.Consequences.Canonicity TR
  open Definition.Typed.Consequences.Consistency TR
  open Definition.Typed.Consequences.Substitution TR
  open Definition.Typed.Properties TR
  open Definition.Untyped Erasure
  open Definition.Untyped.Neutral Erasure type-variant

  open Graded.Context 𝕄
  open Graded.Context.Properties 𝕄
  open Graded.Erasure.SucRed TR
  open Graded.Modality.Properties 𝕄
  open Graded.Mode 𝕄
  open Graded.Usage 𝕄 UR

  private variable
    t : Term _

  -- A counterexample to canonicity. Note that the use of
  -- no-type-restrictions and no-usage-restrictions above means that
  -- erased eliminations are allowed.

  cEx :
    ∃₄ λ (m : Nat) (Γ : Con Term m) (γ : Conₘ m) (t : Term m)
    → Γ ⊢ t ∷ ℕ
    × γ ▸[ 𝟙ᵐ ] t
    × γ PE.≡ 𝟘ᶜ
    × NegativeErasedContext Γ γ
    × Consistent Γ
    × ((∃ λ u → Numeral u × Γ ⊢ t ≡ u ∷ ℕ) → ⊥)
    × ((∃ λ u → Numeral u × Γ ⊢ t ⇒ˢ* u ∷ℕ) → ⊥)
    × (∃ λ u → Γ ⊢ t ↘ u ∷ ℕ × Neutral u)
  cEx =
      _
    , ε ∙ (Σʷ ω , 𝟘 ▷ ℕ ▹ ℕ) , _ , prodrec 𝟘 ω 𝟘 ℕ (var x0) zero
    , ⊢prodrec
    , prodrecₘ {η = 𝟘ᶜ} var zeroₘ
        (sub ℕₘ (≤ᶜ-refl ∙ ≤-reflexive (M.·-zeroʳ _))) _
    , PE.refl
    , ε ∙𝟘
    , inhabited-consistent
        (singleSubst (prodⱼ ε⊢ℕ εℕ⊢ℕ (zeroⱼ ε) (zeroⱼ ε) _))
    , (λ { (.zero , zeroₙ , t≡u) → lem (completeEqTerm t≡u)
         ; (.(suc _) , sucₙ numU , t≡u) → lem′ (completeEqTerm t≡u)
         })
    , (λ { (u , numU , (whred x ⇨ˢ d)) → neRedTerm x (prodrecₙ (var x0))})
    , (_ , (id ⊢prodrec , ne neutral) , neutral)
    where
    open E

    lem :
      ε ∙ (Σʷ ω , 𝟘 ▷ ℕ ▹ ℕ) ⊢
        prodrec 𝟘 ω 𝟘 ℕ (var x0) zero [conv↑] zero ∷ ℕ →
      ⊥
    lem ([↑]ₜ _ _ _ (D , _) (d , _) (d′ , _) _)
      with whnfRed*Term d (ne (prodrecₙ (var x0)))
         | whnfRed*Term d′ zeroₙ
         | whnfRed* D ℕₙ
    lem ([↑]ₜ _ _ _ _ _ _ (ℕ-ins ()))
      | PE.refl | PE.refl | PE.refl
    lem ([↑]ₜ _ _ _ _ _ _ (ne-ins _ _ _ ()))
      | PE.refl | PE.refl | PE.refl

    lem′ :
      ε ∙ (Σʷ ω , 𝟘 ▷ ℕ ▹ ℕ) ⊢
        prodrec 𝟘 ω 𝟘 ℕ (var x0) zero [conv↑] suc t ∷ ℕ →
      ⊥
    lem′ ([↑]ₜ _ _ _ (D , _) (d , _) (d′ , _) _)
      with whnfRed*Term d (ne (prodrecₙ (var x0)))
         | whnfRed*Term d′ sucₙ
         | whnfRed* D ℕₙ
    lem′ ([↑]ₜ _ _ _ _ _ _ (ℕ-ins ()))
      | PE.refl | PE.refl | PE.refl
    lem′ ([↑]ₜ _ _ _ _ _ _ (ne-ins _ _ _ ()))
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
      prodrecⱼ {r = 𝟘} εΣ⊢ℕ εΣℕ⊢ℕ εΣΣ⊢ℕ (var₀ ε⊢Σ) (zeroⱼ ⊢εΣℕℕ)
        _
    neutral = prodrecₙ (var _)

-- If one drops the assumption about erased matches from the statement
-- of Application.NegativeOrErasedAxioms.Canonicity.canonicityEq, then
-- the lemma cannot be proved (assuming that Agda is consistent).

not-canonicityEq :
  (∀ {a} {M : Set a} →
   let open Graded.Modality M
       open Definition.Untyped M
   in
   {𝕄 : Modality} →
   let open Graded.Mode 𝕄
       open Graded.Restrictions 𝕄
       open Modality 𝕄
   in
   ⦃ 𝟘-well-behaved : Has-well-behaved-zero semiring-with-meet ⦄
   (TR : Type-restrictions 𝕄) →
   let open Type-restrictions TR
       open
         Application.NegativeOrErasedAxioms.NegativeOrErasedContext TR
       open Definition.Typed TR
   in
   (UR : Usage-restrictions 𝕄) →
   let open Usage-restrictions UR
       open Graded.Usage 𝕄 UR
   in
   ∀ {m} {Γ : Con Term m} →
   Consistent Γ →
   (∀ {p q} →
    Unitʷ-η → Unitʷ-allowed → Unitrec-allowed 𝟙ᵐ p q →
    𝟙 ≤ 𝟘 ⊎ p PE.≡ 𝟘) →
   ∀ {t γ} → Γ ⊢ t ∷ ℕ → γ ▸[ 𝟙ᵐ ] t → NegativeErasedContext Γ γ →
   ∃ λ u → Numeral u × Γ ⊢ t ≡ u ∷ ℕ) →
  ⊥
not-canonicityEq hyp =
  case Counterexample.cEx (nr-available-and-𝟘ᵐ-allowed-if true) of λ {
    (_ , _ , _ , _ , ⊢t , ▸t , _ , nec , con , not-numeral , _) →
  not-numeral (hyp _ _ con (λ ()) ⊢t ▸t nec) }
