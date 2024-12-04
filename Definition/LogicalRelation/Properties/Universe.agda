------------------------------------------------------------------------
-- Lemmata relating to terms of the universe type
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Properties.Universe
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}

open import Definition.Untyped M
open import Definition.Untyped.Neutral M
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Properties.Escape R
open import Definition.LogicalRelation.Properties.Kit R
open import Definition.LogicalRelation.Irrelevance R

open import Tools.Nat hiding (_<_; _≤_)
open import Tools.Product
open import Tools.Empty
open import Tools.Function

private
  variable
    n : Nat
    l l′ l″ : Universe-level
    Γ : Con Term n
    A B t u : Term _

private opaque

  -- A lemma used below.

  univEq′ :
<<<<<<< HEAD
    (⊩U : Γ ⊩⟨ l ⟩U U t) → Γ ⊩⟨ l ⟩ A ∷ U t / U-intr ⊩U → ∃ λ l′ → Γ ⊩⟨ l′ ⟩ A
  univEq′ (noemb (Uᵣ k [k] k< [ _ , _ , id _ ])) (Uₜ _ _ _ _ ⊩A) =
    _ , ⊩<⇔⊩ k< .proj₁ ⊩A
  univEq′ (noemb (Uᵣ _ _ _ [ _ , _ , U⇒ ⇨ _ ])) _ =
=======
    (⊩U : Γ ⊩⟨ l ⟩U U l′) → Γ ⊩⟨ l ⟩ A ∷ U l′ / U-intr ⊩U → Γ ⊩⟨ l′ ⟩ A
  univEq′ (noemb (Uᵣ _ l< (id _))) (Uₜ _ _ _ _ ⊩A) =
    ⊩<⇔⊩ l< .proj₁ ⊩A
  univEq′ (noemb (Uᵣ _ _ (U⇒ ⇨ _))) _ =
>>>>>>> master
    ⊥-elim (whnfRed U⇒ Uₙ)
  univEq′ (emb p     ⊩U) ⊩A = {!univEq′ ⊩U ⊩A!}

-- Reducible terms of type U are reducible types.
univEq :
  ∀ {l A} ([U] : Γ ⊩⟨ l ⟩ U t) → Γ ⊩⟨ l ⟩ A ∷ U t / [U] → ∃ λ l′ → Γ ⊩⟨ l′ ⟩ A
univEq [U] [A] =
  let Uel = U-elim [U]
  in univEq′ Uel (irrelevanceTerm [U] (U-intr Uel) [A])



private opaque

  -- A lemma used below.

  univEqEq′ :
    (⊩U : Γ ⊩⟨ l ⟩U U t) (⊩A : Γ ⊩⟨ l′ ⟩ A) →
    Γ ⊩⟨ l ⟩ A ≡ B ∷ U t / U-intr ⊩U → Γ ⊩⟨ l′ ⟩ A ≡ B / ⊩A
  univEqEq′ (noemb (Uᵣ k [k] p _)) ⊩A (Uₜ₌ _ _ _ _ _ _ _ ⊩A′ _ A≡B) = {!   !}
  -- univEqEq′ (noemb (Uᵣ k [k] ≤ᵘ-refl _)) ⊩A (Uₜ₌ _ _ _ _ _ _ _ ⊩A′ _ A≡B) =
  --   irrelevanceEq ⊩A′ ⊩A A≡B
  -- univEqEq′
  --   (noemb (Uᵣ k [k] (≤ᵘ-step p) ⇒*U)) ⊩A
  --   (Uₜ₌ _ _ A⇒*A′ B⇒*B′ A′-type B′-type A′≅B′ _ ⊩B A≡B) =
  --   univEqEq′ (noemb (Uᵣ k [k] p ⇒*U)) ⊩A
  --     (Uₜ₌ _ _ A⇒*A′ B⇒*B′ A′-type B′-type A′≅B′ _ ⊩B A≡B)
  univEqEq′ (emb p     ⊩U) = {!univEqEq′ ⊩U!}

-- Reducible term equality of type U is reducible type equality.
univEqEq :
  (⊩U : Γ ⊩⟨ l ⟩ U t) (⊩A : Γ ⊩⟨ l′ ⟩ A) →
  Γ ⊩⟨ l ⟩ A ≡ B ∷ U t / ⊩U →
  Γ ⊩⟨ l′ ⟩ A ≡ B / ⊩A
univEqEq ⊩U ⊩A A≡B =
  let ⊩U′ = U-elim ⊩U in
  univEqEq′ ⊩U′ ⊩A (irrelevanceEqTerm ⊩U (U-intr ⊩U′) A≡B)
