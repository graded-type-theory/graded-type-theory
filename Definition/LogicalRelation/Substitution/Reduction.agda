------------------------------------------------------------------------
-- The logical relation is backwards-closed under valid reductions
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Reduction
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}

open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.Substitution R
open import Definition.Untyped M using (Con ; Term)

open import Tools.Nat
open import Tools.Product

private
  variable
    n : Nat
    Γ : Con Term n

-- Weak head expansion of valid terms.
redSubstTermᵛ : ∀ {Γ : Con Term n} {A t u l}
              → ([Γ] : ⊩ᵛ Γ)
              → Γ ⊩ᵛ t ⇒ u ∷ A / [Γ]
              → ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
              → Γ ⊩ᵛ⟨ l ⟩ u ∷ A / [Γ] / [A]
              → Γ ⊩ᵛ⟨ l ⟩ t ∷ A / [Γ] / [A]
              × Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A / [Γ] / [A]
redSubstTermᵛ [Γ] t⇒u [A] [u] =
  (λ ⊢Δ [σ] →
     let [σA] = proj₁ (unwrap [A] ⊢Δ [σ])
         [σt] , [σt≡σu] = redSubstTerm (t⇒u ⊢Δ [σ])
                                       (proj₁ (unwrap [A] ⊢Δ [σ]))
                                       (proj₁ ([u] ⊢Δ [σ]))
     in  [σt]
     ,   (λ [σ′] [σ≡σ′] →
            let [σ′A] = proj₁ (unwrap [A] ⊢Δ [σ′])
                [σA≡σ′A] = proj₂ (unwrap [A] ⊢Δ [σ]) [σ′] [σ≡σ′]
                [σ′t] , [σ′t≡σ′u] = redSubstTerm (t⇒u ⊢Δ [σ′])
                                                 (proj₁ (unwrap [A] ⊢Δ [σ′]))
                                                 (proj₁ ([u] ⊢Δ [σ′]))
            in  transEqTerm [σA] [σt≡σu]
                            (transEqTerm [σA] ((proj₂ ([u] ⊢Δ [σ])) [σ′] [σ≡σ′])
                                         (convEqTerm₂ [σA] [σ′A] [σA≡σ′A]
                                                      (symEqTerm [σ′A] [σ′t≡σ′u])))))
  , (λ ⊢Δ [σ] → proj₂ (redSubstTerm (t⇒u ⊢Δ [σ])
                                    (proj₁ (unwrap [A] ⊢Δ [σ]))
                                    (proj₁ ([u] ⊢Δ [σ]))))
