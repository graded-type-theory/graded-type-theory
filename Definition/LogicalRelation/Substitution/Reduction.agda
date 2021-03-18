{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Reduction {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution
open import Definition.Untyped using (Con ; Term)

open import Tools.Nat
open import Tools.Product

private
  variable
    n : Nat
    M : Set
    Γ : Con (Term M) n

-- Weak head expansion of valid terms.
redSubstTermᵛ : ∀ {M : Set} {Γ : Con (Term M) n} {A t u l} {p : M}
              → ([Γ] : ⊩ᵛ Γ)
              → Γ ⊩ᵛ t ⇒ u ∷ A / [Γ]
              → ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
              → Γ ⊩ᵛ⟨ l ⟩ u ∷ A / [Γ] / [A]
              → Γ ⊩ᵛ⟨ l ⟩ t ∷ A / [Γ] / [A]
              × Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A / [Γ] / [A]
redSubstTermᵛ {p = p} [Γ] t⇒u [A] [u] =
  (λ ⊢Δ [σ] →
     let [σA] = proj₁ ([A] ⊢Δ [σ])
         [σt] , [σt≡σu] = redSubstTerm {p = p} (t⇒u ⊢Δ [σ])
                                       (proj₁ ([A] ⊢Δ [σ]))
                                       (proj₁ ([u] ⊢Δ [σ]))
     in  [σt]
     ,   (λ [σ′] [σ≡σ′] →
            let [σ′A] = proj₁ ([A] ⊢Δ [σ′])
                [σA≡σ′A] = proj₂ ([A] ⊢Δ [σ]) [σ′] [σ≡σ′]
                [σ′t] , [σ′t≡σ′u] = redSubstTerm {p = p} (t⇒u ⊢Δ [σ′])
                                                 (proj₁ ([A] ⊢Δ [σ′]))
                                                 (proj₁ ([u] ⊢Δ [σ′]))
            in  transEqTerm [σA] [σt≡σu]
                            (transEqTerm [σA] ((proj₂ ([u] ⊢Δ [σ])) [σ′] [σ≡σ′])
                                         (convEqTerm₂ [σA] [σ′A] [σA≡σ′A]
                                                      (symEqTerm [σ′A] [σ′t≡σ′u])))))
  , (λ ⊢Δ [σ] → proj₂ (redSubstTerm {p = p} (t⇒u ⊢Δ [σ])
                                    (proj₁ ([A] ⊢Δ [σ]))
                                    (proj₁ ([u] ⊢Δ [σ]))))
