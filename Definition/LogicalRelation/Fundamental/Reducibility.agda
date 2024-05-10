------------------------------------------------------------------------
-- The fundamental lemma of the logical relation for reducibility.
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Fundamental.Reducibility
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Hidden R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.Reducibility R
open import Definition.LogicalRelation.Fundamental R
open import Definition.LogicalRelation.Irrelevance R

open import Tools.Function
open import Tools.Nat using (Nat)
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
  unfolding _⊩⟨_⟩_≡_

  -- A variant of reducibleEq.

  reducible-⊩≡ : Γ ⊢ A ≡ B → Γ ⊩⟨ ¹ ⟩ A ≡ B
  reducible-⊩≡ = reducibleEq

-- Well-formed terms are reducible.
reducibleTerm : ∀ {t A} → Γ ⊢ t ∷ A → ∃ λ [A] → Γ ⊩⟨ ¹ ⟩ t ∷ A / [A]
reducibleTerm {t = t} {A} ⊢t =
  let [Γ] , [A] , [t] = fundamentalTerm ⊢t
  in  reducibleᵛ [Γ] [A] , reducibleTermᵛ {t = t} {A} [Γ] [A] [t]

opaque
  unfolding _⊩⟨_⟩_∷_

  -- A variant of reducibleTerm.

  reducible-⊩∷ : Γ ⊢ t ∷ A → Γ ⊩⟨ ¹ ⟩ t ∷ A
  reducible-⊩∷ = reducibleTerm

-- Well-formed term equality is reducible.
reducibleEqTerm : ∀ {t u A} → Γ ⊢ t ≡ u ∷ A → ∃ λ [A] → Γ ⊩⟨ ¹ ⟩ t ≡ u ∷ A / [A]
reducibleEqTerm {t = t} {u} {A} t≡u =
  let [Γ] , modelsTermEq [A] [t] [u] [t≡u] = fundamentalTermEq t≡u
  in  reducibleᵛ [Γ] [A] , reducibleEqTermᵛ {t = t} {u} {A} [Γ] [A] [t≡u]

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- A variant of reducibleEqTerm.

  reducible-⊩≡∷ : Γ ⊢ t ≡ u ∷ A → Γ ⊩⟨ ¹ ⟩ t ≡ u ∷ A
  reducible-⊩≡∷ t≡u =
    case fundamentalTermEq t≡u of λ
      (⊩Γ , modelsTermEq ⊩A ⊩t ⊩u t≡u) →
      reducibleᵛ ⊩Γ ⊩A , reducibleTermᵛ ⊩Γ ⊩A ⊩t
    , reducibleTermᵛ ⊩Γ ⊩A ⊩u , reducibleEqTermᵛ ⊩Γ ⊩A t≡u
