------------------------------------------------------------------------
-- The typing relation is an instance of the abstract set of
-- equality relations.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.EqRelInstance
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Weakening R
open import Definition.Typed.Weakening.Definition R
open import Definition.Typed.EqualityRelation R
import Definition.Typed.EqualityRelation.Instance

open import Tools.Function
open import Tools.Level
open import Tools.Product
open import Tools.Relation
open import Tools.Unit

private opaque

  -- A lemma used below.

  equality-relations :
    Equality-relations _»_⊢_≡_ _»_⊢_≡_∷_ _»_⊢_≡_∷_ No-equality-reflection
  equality-relations = λ where
      .Var-included? →
        No-equality-reflection?
      .Equality-reflection-allowed→¬Var-included →
        λ { ok (no-equality-reflection not-ok) → not-ok ok }
      .⊢≡→⊢≅        → λ _ → idᶠ
      .⊢≡∷→⊢≅∷      → λ _ → idᶠ
      .~-to-≅ₜ      → idᶠ
      .≅-eq         → idᶠ
      .≅ₜ-eq        → idᶠ
      .≅-univ       → univ
      .≅-sym        → sym
      .≅ₜ-sym       → sym′
      .~-sym        → sym′
      .≅-trans      → trans
      .≅ₜ-trans     → trans
      .~-trans      → trans
      .≅-conv       → conv
      .~-conv       → conv
      .≅-wk         → wkEq
      .≅ₜ-wk        → wkEqTerm
      .~-wk         → wkEqTerm
      .≅-defn-wk    → defn-wkEq
      .≅ₜ-defn-wk   → defn-wkEqTerm
      .~-defn-wk    → defn-wkEqTerm
      .≅-red        → λ (A⇒* , _) (B⇒* , _) → reduction A⇒* B⇒*
      .≅ₜ-red       → λ (A⇒* , _) (t⇒* , _) (u⇒* , _) →
                        reductionₜ A⇒* t⇒* u⇒*
      .≅-Urefl      → refl ∘ᶠ Uⱼ
      .≅ₜ-ℕrefl     → refl ∘ᶠ ℕⱼ
      .≅ₜ-Emptyrefl → refl ∘ᶠ Emptyⱼ
      .≅ₜ-Unitrefl  → λ ⊢Γ → refl ∘ᶠ Unitⱼ ⊢Γ
      .≅ₜ-η-unit    → η-unit
      .≅-ΠΣ-cong    → ΠΣ-cong
      .≅ₜ-ΠΣ-cong   → ΠΣ-cong
      .≅ₜ-zerorefl  → refl ∘ᶠ zeroⱼ
      .≅-suc-cong   → suc-cong
      .≅-prod-cong  → prod-cong
      .≅-η-eq       → λ ⊢t ⊢u _ _ t0≡u0 → η-eq′ ⊢t ⊢u t0≡u0
      .≅-Σ-η        → λ ⊢t ⊢u _ _ fst≡ snd≡ → Σ-η′ ⊢t ⊢u fst≡ snd≡
      .~-var        → refl
      .~-defn       → λ ⊢α _ → refl ⊢α
      .~-app        → app-cong
      .~-fst        → fst-cong
      .~-snd        → snd-cong
      .~-natrec     → natrec-cong
      .~-prodrec    → prodrec-cong
      .~-emptyrec   → emptyrec-cong
      .~-unitrec    → unitrec-cong
      .≅ₜ-starrefl  → λ ⊢Γ ok → refl (starⱼ ⊢Γ ok)
      .≅-Id-cong    → Id-cong
      .≅ₜ-Id-cong   → Id-cong
      .≅ₜ-rflrefl   → refl ∘ᶠ rflⱼ
      .~-J          → J-cong
      .~-K          → K-cong
      .~-[]-cong    → []-cong-cong
    where
    open Equality-relations

-- An EqRelSet instance that uses definitional equality (_⊢_≡_ and
-- _⊢_≡_∷_). Neutrals are included if and only if equality reflection
-- is not allowed.

instance

  eqRelInstance : EqRelSet
  eqRelInstance = λ where
    .EqRelSet._»_⊢_≅_            → _»_⊢_≡_
    .EqRelSet._»_⊢_≅_∷_          → _»_⊢_≡_∷_
    .EqRelSet._»_⊢_~_∷_          → _»_⊢_≡_∷_
    .EqRelSet.Var-included       → No-equality-reflection
    .EqRelSet.equality-relations → equality-relations

open EqRelSet eqRelInstance public
