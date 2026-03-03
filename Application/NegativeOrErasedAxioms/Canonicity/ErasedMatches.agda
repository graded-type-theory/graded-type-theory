------------------------------------------------------------------------
-- If erased matches are allowed, then erased axioms do jeopardize
-- canonicity
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
open import Tools.Unit

import Application.NegativeOrErasedAxioms.NegativeOrErasedContext

import Definition.Conversion
import Definition.Conversion.Consequences.Completeness
import Definition.Typed
import Definition.Typed.Consequences.Canonicity
import Definition.Typed.Consequences.Consistency
import Definition.Typed.Properties
open import Definition.Typed.Restrictions
import Definition.Typed.Substitution
import Definition.Untyped
import Definition.Untyped.Neutral
import Definition.Untyped.Whnf

import Graded.Context
import Graded.Context.Properties
import Graded.Erasure.SucRed
import Graded.Modality
import Graded.Modality.Properties
import Graded.Mode.Instances.Zero-one
import Graded.Restrictions.Zero-one
import Graded.Usage
open import Graded.Usage.Restrictions
open import Graded.Usage.Restrictions.Natrec
open import Graded.Mode.Instances.Zero-one.Variant

open import Graded.Modality.Instances.Erasure as E using (Erasure)
import Graded.Modality.Instances.Erasure.Modality as EM

module Counterexample
  (variant : Mode-variant EM.ErasureModality)
  where

  open Graded.Modality Erasure
  open Graded.Mode.Instances.Zero-one variant

  private

    -- The modality used in this local module.

    𝕄 = EM.ErasureModality

    module M = Modality 𝕄

    open Graded.Restrictions.Zero-one 𝕄 variant

    -- The type and usage restrictions used in this local module.

    TR : Type-restrictions 𝕄
    TR = no-type-restrictions true false

    UR : Usage-restrictions 𝕄 Zero-one-isMode
    UR = no-usage-restrictions Nr true true

  open Type-restrictions TR
  open Usage-restrictions UR

  private instance

    -- Equality reflection is not allowed.

    not-ok : No-equality-reflection
    not-ok = No-equality-reflection⇔ .proj₂ (λ { (lift ()) })

  open Application.NegativeOrErasedAxioms.NegativeOrErasedContext TR

  open Definition.Conversion TR
  open Definition.Conversion.Consequences.Completeness TR
  open Definition.Typed TR
  open Definition.Typed.Consequences.Canonicity TR
  open Definition.Typed.Consequences.Consistency TR
  open Definition.Typed.Properties TR
  open Definition.Typed.Substitution TR
  open Definition.Untyped Erasure
  open Definition.Untyped.Neutral Erasure type-variant
  open Definition.Untyped.Whnf Erasure type-variant

  open Graded.Context 𝕄
  open Graded.Context.Properties 𝕄
  open Graded.Erasure.SucRed TR
  open Graded.Modality.Properties 𝕄
  open Graded.Usage UR

  private variable
    t : Term _

  -- A counterexample to canonicity. Note that the use of
  -- no-type-restrictions and no-usage-restrictions above means that
  -- erased eliminations are allowed.

  cEx :
    ∃₅ λ (m n : Nat) (Γ : Cons m n) (γ : Conₘ n) (t : Term n)
    → Γ ⊢ t ∷ ℕ
    × ▸[ 𝟙ᵐ ] Γ .defs
    × γ ▸[ 𝟙ᵐ ] t
    × γ PE.≡ 𝟘ᶜ
    × NegativeErasedContext Γ γ
    × Consistent Γ
    × (∀ {p q} →
       Unitʷ-η → Unitʷ-allowed → Unitrec-allowed 𝟙ᵐ p q →
       M.𝟙 M.≤ M.𝟘 ⊎ p PE.≡ M.𝟘)
    × No-equality-reflection or-empty Γ .vars
    × ((∃ λ u → Numeral u × Γ ⊢ t ≡ u ∷ ℕ) → ⊥)
    × ((∃ λ u → Numeral u × Γ ⊢ t ⇒ˢ* u ∷ℕ) → ⊥)
    × (∃ λ u → Γ ⊢ t ↘ u ∷ ℕ × Neutral⁺ (Γ .defs) u)
  cEx =
      _
    , _
    , ε » ε ∙ (Σʷ ω , 𝟘 ▷ ℕ ▹ ℕ) , _ , prodrec 𝟘 ω 𝟘 ℕ (var x0) zero
    , ⊢prodrec
    , (λ ())
    , prodrecₘ {η = 𝟘ᶜ} var zeroₘ
        (sub ℕₘ (≤ᶜ-refl ∙ ≤-reflexive (M.·-zeroʳ _))) _
    , PE.refl
    , ε ε ∙𝟘
    , inhabited-consistent
        (⊢ˢʷ∷-sgSubst (prodⱼ εℕ⊢ℕ (zeroⱼ εε) (zeroⱼ εε) _))
    , (λ ())
    , possibly-nonempty
    , (λ { (.zero , zeroₙ , t≡u) → lem (completeEqTerm t≡u)
         ; (.(suc _) , sucₙ numU , t≡u) → lem′ (completeEqTerm t≡u)
         })
    , (λ where
         (u , numU , whred x ⇨ˢ d) → neRedTerm x (prodrecₙ (var tt x0))
         (_ , ()   , id _))
    , (_ , (id ⊢prodrec , ne neutral) , neutral)
    where
    open E

    lem :
      ε » ε ∙ Σʷ ω , 𝟘 ▷ ℕ ▹ ℕ ⊢
        prodrec 𝟘 ω 𝟘 ℕ (var x0) zero [conv↑] zero ∷ ℕ →
      ⊥
    lem ([↑]ₜ _ _ _ (D , _) (d , _) (d′ , _) prodrec-0-zero≡zero) =
      case whnfRed*Term d (ne (prodrecₙ (var _ x0))) of λ {
        PE.refl →
      case whnfRed*Term d′ zeroₙ of λ {
        PE.refl →
      case whnfRed* D ℕₙ of λ {
        PE.refl →
      case prodrec-0-zero≡zero of λ where
         (ℕ-ins ([~] _ _ ()))
         (ne-ins _ _ _ ([~] _ _ ())) }}}

    lem′ :
      ε » ε ∙ Σʷ ω , 𝟘 ▷ ℕ ▹ ℕ ⊢
        prodrec 𝟘 ω 𝟘 ℕ (var x0) zero [conv↑] suc t ∷ ℕ →
      ⊥
    lem′ ([↑]ₜ _ _ _ (D , _) (d , _) (d′ , _) prodrec-0-zero≡suc) =
      case whnfRed*Term d (ne (prodrecₙ (var _ x0))) of λ {
        PE.refl →
      case whnfRed*Term d′ sucₙ of λ {
        PE.refl →
      case whnfRed* D ℕₙ of λ {
        PE.refl →
      case prodrec-0-zero≡suc of λ where
         (ℕ-ins ([~] _ _ ()))
         (ne-ins _ _ _ ([~] _ _ ())) }}}

    ⊢εℕ = ∙ ⊢ℕ εε
    εℕ⊢ℕ = ⊢ℕ ⊢εℕ
    ε⊢Σ = ΠΣⱼ εℕ⊢ℕ _
    ⊢εΣ = ∙ ε⊢Σ
    ⊢εΣℕ = ∙ ⊢ℕ ⊢εΣ
    εΣℕ⊢ℕ = ⊢ℕ ⊢εΣℕ
    εΣ⊢Σ = ΠΣⱼ εΣℕ⊢ℕ _
    ⊢εΣΣ = ∙ εΣ⊢Σ
    εΣΣ⊢ℕ = ⊢ℕ ⊢εΣΣ
    ⊢εΣℕℕ = ∙ εΣℕ⊢ℕ
    ⊢prodrec = prodrecⱼ {r = 𝟘} εΣΣ⊢ℕ (var₀ ε⊢Σ) (zeroⱼ ⊢εΣℕℕ) _
    neutral = prodrecₙ (var _ _)

-- If one drops the assumption about erased matches from the statement
-- of Application.NegativeOrErasedAxioms.Canonicity.canonicityEq, then
-- the lemma cannot be proved (assuming that Agda is consistent).

not-canonicityEq :
  (∀ {a} {M : Set a} →
   let open Graded.Modality M
       open Definition.Untyped M
   in
   {𝕄 : Modality} →
   {variant : Mode-variant 𝕄} →
   let open Graded.Restrictions.Zero-one 𝕄 variant
       open Modality 𝕄
       open Graded.Mode.Instances.Zero-one variant
   in
   ⦃ 𝟘-well-behaved : Has-well-behaved-zero semiring-with-meet ⦄
   (TR : Type-restrictions 𝕄) →
   let open Type-restrictions TR
       open
         Application.NegativeOrErasedAxioms.NegativeOrErasedContext TR
       open Definition.Typed TR
   in
   (UR : Usage-restrictions 𝕄 Zero-one-isMode) →
   let open Usage-restrictions UR
       open Graded.Usage UR
   in
   ∀ {m n} {Γ : Cons m n} →
   Consistent Γ →
   (∀ {p q} →
    Unitʷ-η → Unitʷ-allowed → Unitrec-allowed 𝟙ᵐ p q →
    𝟙 ≤ 𝟘 ⊎ p PE.≡ 𝟘) →
   ⦃ ok : No-equality-reflection or-empty Γ .vars ⦄ →
   ▸[ 𝟙ᵐ ] Γ .defs →
   ∀ {t γ} → Γ ⊢ t ∷ ℕ → γ ▸[ 𝟙ᵐ ] t → NegativeErasedContext Γ γ →
   ∃ λ u → Numeral u × Γ ⊢ t ≡ u ∷ ℕ) →
  ⊥
not-canonicityEq hyp =
  case Counterexample.cEx (𝟘ᵐ-Allowed _) of λ {
    (_ , _ , _ , _ , _ ,
     ⊢t , ▸Γ , ▸t , _ , nec , con , ok₁ , ok₂ , not-numeral , _) →
  not-numeral $
  hyp _ _ con (λ {q = q} → ok₁ {q = q}) ⦃ ok = ok₂ ⦄ ▸Γ ⊢t ▸t nec }
