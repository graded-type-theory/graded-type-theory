------------------------------------------------------------------------
-- Cumulativity lemmata for the logical relation
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Properties.Cumulativity
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.Untyped M hiding (K)
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties.Reflexivity R

open import Tools.Empty
open import Tools.Function
open import Tools.Nat hiding (_<_)
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n
    A B t u : Term n
    l : TypeLevel
    b : BinderMode
    s : Strength
    p q : M

opaque mutual
  -- Well-formness is cumulative
  cumul : ∀ {l l′ A} → l < l′ → Γ ⊩⟨ l ⟩ A →  Γ ⊩⟨ l′ ⟩ A
  cumul ≤′-refl ⊩Ty = cumulStep ⊩Ty
  cumul (≤′-step l<) ⊩Ty = cumulStep (cumul l< ⊩Ty)

  cumulStep : ∀ {l A} → Γ ⊩⟨ l ⟩ A →  Γ ⊩⟨ 1+ l ⟩ A
  cumulStep (Uᵣ′ l′ l< ⇒*U) = Uᵣ′ l′ (≤′-step l<) ⇒*U
  cumulStep (ℕᵣ x) =  ℕᵣ x
  cumulStep (Emptyᵣ x) =  Emptyᵣ x
  cumulStep (Unitᵣ x) =  Unitᵣ x
  cumulStep (ne′ K D neK K≡K) = ne′ K D neK K≡K
  cumulStep (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext ok) =
    (Bᵣ′ W F G D ⊢F ⊢G A≡A (λ x x₁ → cumulStep ([F] x x₁))
    (λ [ρ] ⊢Δ x → cumulStep ([G]  [ρ] ⊢Δ
      (irrelevanceTerm (cumulStep ([F] [ρ] ⊢Δ)) ([F] [ρ] ⊢Δ) x)))
    (λ [ρ] ⊢Δ [a] [b] x →
      cumulEq ≤′-refl ([G] [ρ] ⊢Δ (irrelevanceTerm (cumulStep ([F] [ρ] ⊢Δ)) ([F] [ρ] ⊢Δ) [a]))
      (G-ext [ρ] ⊢Δ
        (irrelevanceTerm (cumulStep ([F] [ρ] ⊢Δ)) ([F] [ρ] ⊢Δ) [a])
        (irrelevanceTerm (cumulStep ([F] [ρ] ⊢Δ)) ([F] [ρ] ⊢Δ) [b])
        (irrelevanceEqTerm (cumulStep ([F] [ρ] ⊢Δ)) ([F] [ρ] ⊢Δ) x)))
    ok)
  cumulStep (Idᵣ (Idᵣ Ty lhs rhs ⇒*Id ⊩Ty ⊩lhs ⊩rhs)) =  Idᵣ
          (Idᵣ Ty lhs rhs ⇒*Id (cumul ≤′-refl ⊩Ty) (cumulTerm ≤′-refl  ⊩Ty ⊩lhs) (cumulTerm ≤′-refl  ⊩Ty ⊩rhs))
  cumulStep (emb l< [A]) = emb (≤′-step l<) [A]

  cumulTerm : ∀ {l l′ A t} → (l< : l < l′) → ([A] : Γ ⊩⟨ l ⟩ A)
                → Γ ⊩⟨ l ⟩ t ∷ A / [A]
                → Γ ⊩⟨ l′ ⟩ t ∷ A / cumul l< [A]
  cumulTerm l< ⊩Ty ⊩Tm = irrelevanceTerm ⊩Ty (cumul l< ⊩Ty) ⊩Tm

  cumulEq :
    ∀ {l l′ A B} → (l< : l < l′) →
    (⊩A : Γ ⊩⟨ l ⟩ A) →
    Γ ⊩⟨ l ⟩ A ≡ B / ⊩A →
    Γ ⊩⟨ l′ ⟩ A ≡ B / (cumul l< ⊩A)
  cumulEq l< ⊩A eq = irrelevanceEq  ⊩A (cumul l< ⊩A) eq

  cumulTermEq :
      ∀ {l l′ A t u} → (l< : l < l′) →
      (⊩A : Γ ⊩⟨ l ⟩ A) →
      Γ ⊩⟨ l ⟩ t ≡ u ∷ A / ⊩A →
      Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A / cumul l< ⊩A
  cumulTermEq l< ⊩A teq = irrelevanceEqTerm ⊩A (cumul l< ⊩A) teq
