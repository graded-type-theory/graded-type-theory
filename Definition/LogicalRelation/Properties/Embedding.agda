------------------------------------------------------------------------
-- Some embedding lemmas
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Properties.Embedding
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}

open import Definition.Untyped M
open import Definition.Untyped.Properties M
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Properties.Kit R
open import Definition.LogicalRelation.Irrelevance R

open import Tools.Function
open import Tools.Nat using (Nat)

private
  variable
    m n     : Nat
    Γ       : Cons m n
    A B t u : Term n
    l₁ l₂   : Universe-level

opaque

  -- If l₁ <ᵘ l₂, then Γ ⊩⟨ l₁ ⟩ A is contained in Γ ⊩⟨ l₂ ⟩ A.

  emb-≤-⊩ : ∀ {l₁ l₂} → l₁ ≤ᵘ l₂ → Γ ⊩⟨ l₁ ⟩ A → Γ ⊩⟨ l₂ ⟩ A

  -- An embedding lemma for _⊩⟨_⟩_∷_/_.

  emb-≤-⊩∷ :
    {⊩A : Γ ⊩⟨ l₁ ⟩ A} {p : l₁ ≤ᵘ l₂} →
    Γ ⊩⟨ l₁ ⟩ t ∷ A / ⊩A →
    Γ ⊩⟨ l₂ ⟩ t ∷ A / emb-≤-⊩ p ⊩A
  emb-≤-⊩∷ {⊩A} {p} = irrelevanceTerm ⊩A (emb-≤-⊩ p ⊩A)

  emb-≤-⊩ p (Levelᵣ x) = Levelᵣ x
  emb-≤-⊩ p (Uᵣ′ k [k] k< A⇒) = Uᵣ′ k [k] (<ᵘ-≤ᵘ-trans k< p) A⇒
  emb-≤-⊩ p (Liftᵣ′ D [k] [F]) = Liftᵣ′ D [k] (emb-≤-⊩ p [F])
  emb-≤-⊩ p (ℕᵣ x) = ℕᵣ x
  emb-≤-⊩ p (Emptyᵣ x) = Emptyᵣ x
  emb-≤-⊩ p (Unitᵣ′ A⇒ ok) = Unitᵣ′ A⇒ ok
  emb-≤-⊩ p (ne′ k D neK K≡K) = ne′ k D neK K≡K
  emb-≤-⊩ p (Bᵣ′ W F G D A≡A [F] [G] G-ext ok) = Bᵣ′ W F G D A≡A
    (λ [ρ] → emb-≤-⊩ p ([F] [ρ]))
    (λ [ρ] [a] →
       emb-≤-⊩ p $ [G] [ρ] $
       irrelevanceTerm (emb-≤-⊩ p ([F] [ρ])) ([F] [ρ]) [a])
    (λ [ρ] [a] [b] a≡b → irrelevanceEq _ _ $ G-ext [ρ]
        (irrelevanceTerm (emb-≤-⊩ p ([F] [ρ])) ([F] [ρ]) [a])
        (irrelevanceTerm (emb-≤-⊩ p ([F] [ρ])) ([F] [ρ]) [b])
        (irrelevanceEqTerm (emb-≤-⊩ p ([F] [ρ])) ([F] [ρ]) a≡b))
    ok
  emb-≤-⊩ p (Idᵣ (Idᵣ Ty lhs rhs ⇒*Id ⊩Ty ⊩lhs ⊩rhs)) =
    Idᵣ (Idᵣ Ty lhs rhs ⇒*Id (emb-≤-⊩ p ⊩Ty) (emb-≤-⊩∷ {⊩A = ⊩Ty} ⊩lhs) (emb-≤-⊩∷ {⊩A = ⊩Ty} ⊩rhs))
  emb-≤-⊩ p (Quot ⊩A) =
    Quot record
      { ⇒*Quot = ⇒*Quot
      ; ≅Quot  = ≅Quot
      ; ⊩Data  = λ ⊢ρ → emb-≤-⊩ p (⊩Data ⊢ρ)
      ; ⊩Rel   = λ ⊢ρ ⊩t ⊩u →
          emb-≤-⊩ p $
          ⊩Rel ⊢ρ (irrelevanceTerm (emb-≤-⊩ p (⊩Data _)) (⊩Data _) ⊩t)
            (irrelevanceTerm (emb-≤-⊩ p (⊩Data _)) (⊩Data _) ⊩u)
      ; Rel≡Rel = λ ⊢ρ ⊩t₁ ⊩t₂ ⊩u₁ ⊩u₂ t₁≡t₂ u₁≡u₂ →
          irrelevanceEq _ _ $
          Rel≡Rel ⊢ρ
            (irrelevanceTerm (emb-≤-⊩ p (⊩Data _)) (⊩Data _) ⊩t₁)
            (irrelevanceTerm (emb-≤-⊩ p (⊩Data _)) (⊩Data _) ⊩t₂)
            (irrelevanceTerm (emb-≤-⊩ p (⊩Data _)) (⊩Data _) ⊩u₁)
            (irrelevanceTerm (emb-≤-⊩ p (⊩Data _)) (⊩Data _) ⊩u₂)
            (irrelevanceEqTerm (emb-≤-⊩ p (⊩Data _)) (⊩Data _) t₁≡t₂)
            (irrelevanceEqTerm (emb-≤-⊩ p (⊩Data _)) (⊩Data _) u₁≡u₂)
      }
    where
    open _⊩ₗQuot_ ⊩A

opaque

  -- An embedding lemma for _⊩⟨_⟩_≡_/_.

  emb-≤-⊩≡ :
    {⊩A : Γ ⊩⟨ l₁ ⟩ A} {p : l₁ ≤ᵘ l₂} →
    Γ ⊩⟨ l₁ ⟩ A ≡ B / ⊩A → Γ ⊩⟨ l₂ ⟩ A ≡ B / emb-≤-⊩ p ⊩A
  emb-≤-⊩≡ {⊩A} {p} = irrelevanceEq ⊩A (emb-≤-⊩ p ⊩A)

opaque

  -- An embedding lemma for _⊩⟨_⟩_≡_∷_/_.

  emb-≤-⊩≡∷ :
    {⊩A : Γ ⊩⟨ l₁ ⟩ A} {p : l₁ ≤ᵘ l₂} →
    Γ ⊩⟨ l₁ ⟩ t ≡ u ∷ A / ⊩A → Γ ⊩⟨ l₂ ⟩ t ≡ u ∷ A / emb-≤-⊩ p ⊩A
  emb-≤-⊩≡∷ {⊩A} {p} = irrelevanceEqTerm ⊩A (emb-≤-⊩ p ⊩A)
