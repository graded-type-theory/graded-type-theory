------------------------------------------------------------------------
-- The fundamental lemma of the logical relation for reducibility.
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions

module Definition.LogicalRelation.Fundamental.Reducibility
  {a} {M : Set a}
  (R : Type-restrictions M)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.Reducibility R
open import Definition.LogicalRelation.Fundamental R
open import Definition.LogicalRelation.Irrelevance R

open import Tools.Function
open import Tools.Nat
open import Tools.Product

private
  variable
    n : Nat
    Γ : Con Term n
    A B t u : Term _
    l : TypeLevel

-- Well-formed types are reducible.
reducible : ∀ {A} → Γ ⊢ A → Γ ⊩⟨ ¹ ⟩ A
reducible A = let [Γ] , [A] = fundamental A
              in  reducibleᵛ [Γ] [A]

-- Well-formed equality is reducible.
reducibleEq : ∀ {A B} → Γ ⊢ A ≡ B
            → ∃₂ λ [A] ([B] : Γ ⊩⟨ ¹ ⟩ B) → Γ ⊩⟨ ¹ ⟩ A ≡ B / [A]
reducibleEq {A = A} {B} A≡B =
  let [Γ] , [A] , [B] , [A≡B] = fundamentalEq A≡B
  in  reducibleᵛ [Γ] [A]
  ,   reducibleᵛ [Γ] [B]
  ,   reducibleEqᵛ {A = A} {B} [Γ] [A] [A≡B]

opaque

  -- A variant of reducibleEq.

  reducibleEq′ : (⊩A : Γ ⊩⟨ l ⟩ A) → Γ ⊢ A ≡ B → Γ ⊩⟨ l ⟩ A ≡ B / ⊩A
  reducibleEq′ ⊩A A≡B =
    case reducibleEq A≡B of λ {
      (⊩A′ , _ , ⊩A≡B) →
    irrelevanceEq ⊩A′ ⊩A ⊩A≡B }

-- Well-formed terms are reducible.
reducibleTerm : ∀ {t A} → Γ ⊢ t ∷ A → ∃ λ [A] → Γ ⊩⟨ ¹ ⟩ t ∷ A / [A]
reducibleTerm {t = t} {A} ⊢t =
  let [Γ] , [A] , [t] = fundamentalTerm ⊢t
  in  reducibleᵛ [Γ] [A] , reducibleTermᵛ {t = t} {A} [Γ] [A] [t]

opaque

  -- A variant of reducibleTerm.

  reducibleTerm′ : (⊩A : Γ ⊩⟨ l ⟩ A) → Γ ⊢ t ∷ A → Γ ⊩⟨ l ⟩ t ∷ A / ⊩A
  reducibleTerm′ ⊩A ⊢t =
    case reducibleTerm ⊢t of λ {
      (⊩A′ , ⊩t) →
    irrelevanceTerm ⊩A′ ⊩A ⊩t }

-- Well-formed term equality is reducible.
reducibleEqTerm : ∀ {t u A} → Γ ⊢ t ≡ u ∷ A → ∃ λ [A] → Γ ⊩⟨ ¹ ⟩ t ≡ u ∷ A / [A]
reducibleEqTerm {t = t} {u} {A} t≡u =
  let [Γ] , modelsTermEq [A] [t] [u] [t≡u] = fundamentalTermEq t≡u
  in  reducibleᵛ [Γ] [A] , reducibleEqTermᵛ {t = t} {u} {A} [Γ] [A] [t≡u]

opaque

  -- A variant of reducibleEqTerm.

  reducibleEqTerm′ :
    (⊩A : Γ ⊩⟨ l ⟩ A) → Γ ⊢ t ≡ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / ⊩A
  reducibleEqTerm′ ⊩A t≡u =
    case reducibleEqTerm t≡u of λ {
      (⊩A′ , ⊩t≡u) →
    irrelevanceEqTerm ⊩A′ ⊩A ⊩t≡u }
