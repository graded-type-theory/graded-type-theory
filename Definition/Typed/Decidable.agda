------------------------------------------------------------------------
-- Decidability of typing.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
import Tools.PropositionalEquality as PE
open import Tools.Relation as Dec

module Definition.Typed.Decidable
  {a} {M : Set a}
  (R : Type-restrictions M)
  (open Type-restrictions R)
  -- Equality is assumed to be decidable for M.
  (_≟_ : Decidable (PE._≡_ {A = M}))
  -- It is decidable whether the Unit type is allowed.
  (Unit-ok? : Dec Unit-allowed)
  -- ΠΣ-allowed is pointwise decidable.
  (ΠΣ-ok? : ∀ b p q → Dec (ΠΣ-allowed b p q))
  where

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed R
open import Definition.Typed.Consequences.Syntactic R
open import Definition.Typed.Properties R
open import Definition.Typechecking R
open import Definition.Typechecking.Soundness R
open import Definition.Typechecking.Completeness R
open import Definition.Typechecking.Decidable R _≟_ Unit-ok? ΠΣ-ok?

open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product

private
  variable
    n : Nat
    Γ : Con Term n
    A t : Term n

-- Re-export decidability of type and term equality
open import Definition.Typed.Decidable.Equality R _≟_ public

-- If Γ is well-formed and A is checkable, then Γ ⊢ A is decidable.

dec : ⊢ Γ → Checkable A → Dec (Γ ⊢ A)
dec ⊢Γ A =
  Dec.map (soundness⇇Type ⊢Γ) (completeness⇇Type A) (dec⇇Type ⊢Γ A)

-- Type-checking for well-formed types: if Γ ⊢ A holds and t is
-- checkable, then Γ ⊢ t ∷ A is decidable.

decTermᶜ : Γ ⊢ A → Checkable t → Dec (Γ ⊢ t ∷ A)
decTermᶜ ⊢A t = Dec.map (soundness⇇ ⊢Γ) (completeness⇇ t) (dec⇇ ⊢Γ t ⊢A)
  where
  ⊢Γ = wf ⊢A

-- Type-checking for arbitrary checkable types: if Γ is well-formed
-- and A and t are checkable, then Γ ⊢ t ∷ A is decidable.

decTermTypeᶜ : ⊢ Γ → Checkable A → Checkable t → Dec (Γ ⊢ t ∷ A)
decTermTypeᶜ ⊢Γ A t =
  case dec ⊢Γ A of λ where
    (yes ⊢A) → decTermᶜ ⊢A t
    (no ¬⊢A) → no (¬⊢A ∘→ syntacticTerm)

-- Type inference: if ⊢ Γ holds and t is inferable, then
-- ∃ λ A → Γ ⊢ t ∷ A is decidable.

decTermᵢ : ⊢ Γ → Inferable t → Dec (∃ λ A → Γ ⊢ t ∷ A)
decTermᵢ ⊢Γ t = Dec.map
  (λ { (A , t⇉A) → A , (proj₂ (soundness⇉ ⊢Γ t⇉A))})
  (λ { (A , ⊢t)  → _ , (proj₁ (proj₂ (completeness⇉ t ⊢t)))})
  (dec⇉ ⊢Γ t)

-- If Γ is a checkable context, then ⊢ Γ is decidable.

decWfCon : CheckableCon Γ → Dec (⊢ Γ)
decWfCon ε = yes ε
decWfCon (Γ ∙ A) = case decWfCon Γ of λ where
  (yes ⊢Γ) → case dec ⊢Γ A of λ where
    (yes ⊢A) → yes (⊢Γ ∙ ⊢A)
    (no ⊬A) → no λ where
      (⊢Γ ∙ ⊢A) → ⊬A ⊢A
  (no ⊬Γ) → no λ where
    (⊢Γ ∙ ⊢A) → ⊬Γ ⊢Γ

-- If Γ and A are checkable, then Γ ⊢ A is decidable.

decConTypeᶜ : CheckableCon Γ → Checkable A → Dec (Γ ⊢ A)
decConTypeᶜ Γ A =
  case decWfCon Γ of λ where
    (yes ⊢Γ) → dec ⊢Γ A
    (no ¬⊢Γ) → no (¬⊢Γ ∘→ wf)

-- Type-checking for arbitrary checkable contexts and types: if Γ, A
-- and t are checkable, then Γ ⊢ t ∷ A is decidable.

decConTermTypeᶜ :
  CheckableCon Γ → Checkable A → Checkable t → Dec (Γ ⊢ t ∷ A)
decConTermTypeᶜ Γ A t =
  case decWfCon Γ of λ where
    (yes ⊢Γ) → decTermTypeᶜ ⊢Γ A t
    (no ¬⊢Γ) → no (¬⊢Γ ∘→ wfTerm)

-- Type inference for arbitrary checkable contexts: if Γ is checkable
-- and t is inferable, then ∃ λ A → Γ ⊢ t ∷ A is decidable.

decConTermᵢ : CheckableCon Γ → Inferable t → Dec (∃ λ A → Γ ⊢ t ∷ A)
decConTermᵢ Γ t =
  case decWfCon Γ of λ where
    (yes ⊢Γ) → decTermᵢ ⊢Γ t
    (no ¬⊢Γ) → no (¬⊢Γ ∘→ wfTerm ∘→ proj₂)
