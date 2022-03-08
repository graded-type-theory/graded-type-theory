{-# OPTIONS --without-K --safe  #-}

open import Definition.Typed.EqualityRelation
open import Tools.Relation

module Definition.LogicalRelation.Substitution.Reducibility {a ℓ} (M′ : Setoid a ℓ)
                                                            {{eqrel : EqRelSet M′}} where
open EqRelSet {{...}}
open Setoid M′ using () renaming (Carrier to M)

open import Definition.Untyped M hiding (_∷_)
open import Definition.Untyped.Properties M
open import Definition.Typed M′
open import Definition.LogicalRelation M′
open import Definition.LogicalRelation.Irrelevance M′
open import Definition.LogicalRelation.Substitution M′
open import Definition.LogicalRelation.Substitution.Properties M′

open import Tools.Nat
open import Tools.Product

private
  variable
    n : Nat
    Γ : Con Term n

-- Valid types are reducible.
reducibleᵛ : ∀ {A l}
             ([Γ] : ⊩ᵛ Γ)
           → Γ ⊩ᵛ⟨ l ⟩ A / [Γ]
           → Γ ⊩⟨ l ⟩ A
reducibleᵛ [Γ] [A] =
  let ⊢Γ = soundContext [Γ]
      [id] = idSubstS [Γ]
  in  irrelevance′ (subst-id _) (proj₁ ([A] ⊢Γ [id]))

-- Valid type equality is reducible.
reducibleEqᵛ : ∀ {A B l}
               ([Γ] : ⊩ᵛ Γ)
               ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
             → Γ ⊩ᵛ⟨ l ⟩ A ≡ B / [Γ] / [A]
             → Γ ⊩⟨ l ⟩ A ≡ B / reducibleᵛ [Γ] [A]
reducibleEqᵛ {A = A} [Γ] [A] [A≡B] =
  let [σA] = reducibleᵛ {A = A} [Γ] [A]
      ⊢Γ = soundContext [Γ]
      [id] = idSubstS [Γ]
  in  irrelevanceEq″ (subst-id _) (subst-id _)
                      (proj₁ ([A] ⊢Γ [id])) [σA] ([A≡B] ⊢Γ [id])

-- Valid terms are reducible.
reducibleTermᵛ : ∀ {t A l}
                 ([Γ] : ⊩ᵛ Γ)
                 ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
               → Γ ⊩ᵛ⟨ l ⟩ t ∷ A / [Γ] / [A]
               → Γ ⊩⟨ l ⟩ t ∷ A / reducibleᵛ [Γ] [A]
reducibleTermᵛ {A = A} [Γ] [A] [t] =
  let [σA] = reducibleᵛ {A = A} [Γ] [A]
      ⊢Γ = soundContext [Γ]
      [id] = idSubstS [Γ]
  in  irrelevanceTerm″ (subst-id _) (subst-id _)
                        (proj₁ ([A] ⊢Γ [id])) [σA] (proj₁ ([t] ⊢Γ [id]))

-- Valid term equality is reducible.
reducibleEqTermᵛ : ∀ {t u A l}
                   ([Γ] : ⊩ᵛ Γ)
                   ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
                 → Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A / [Γ] / [A]
                 → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / reducibleᵛ [Γ] [A]
reducibleEqTermᵛ {A = A} [Γ] [A] [t≡u] =
  let [σA] = reducibleᵛ {A = A} [Γ] [A]
      ⊢Γ = soundContext [Γ]
      [id] = idSubstS [Γ]
  in  irrelevanceEqTerm″ (subst-id _) (subst-id _) (subst-id _)
                          (proj₁ ([A] ⊢Γ [id])) [σA] ([t≡u] ⊢Γ [id])
