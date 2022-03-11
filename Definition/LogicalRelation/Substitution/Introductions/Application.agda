{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation
open import Tools.Relation

module Definition.LogicalRelation.Substitution.Introductions.Application {a ℓ} (M′ : Setoid a ℓ)
                                                                         {{eqrel : EqRelSet M′}} where
open EqRelSet {{...}}
open Setoid M′ using (_≈_) renaming (Carrier to M)

open import Definition.Untyped M hiding (_∷_)
open import Definition.Untyped.Properties M
open import Definition.Typed M′
open import Definition.LogicalRelation M′
open import Definition.LogicalRelation.Irrelevance M′
open import Definition.LogicalRelation.Properties M′
open import Definition.LogicalRelation.Application M′
open import Definition.LogicalRelation.Substitution M′
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst M′

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n
    p p′ p₁ p₂ q : M

-- Application of valid terms.
appᵛ : ∀ {F G t u l}
       ([Γ] : ⊩ᵛ Γ)
       ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
       ([ΠFG] : Γ ⊩ᵛ⟨ l ⟩ Π p , q ▷ F ▹ G / [Γ])
       ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Π _ , _ ▷ F ▹ G / [Γ] / [ΠFG])
       ([u] : Γ ⊩ᵛ⟨ l ⟩ u ∷ F / [Γ] / [F])
     → p ≈ p′
     → Γ ⊩ᵛ⟨ l ⟩ t ∘ p′ ▷ u ∷ G [ u ] / [Γ] / substSΠ {F = F} {G} {u} BΠ! [Γ] [F] [ΠFG] [u]
appᵛ {F = F} {G} {t} {u} [Γ] [F] [ΠFG] [t] [u] p≈p′ {σ = σ} ⊢Δ [σ] =
  let [G[u]] = substSΠ {F = F} {G} {u} BΠ! [Γ] [F] [ΠFG] [u]
      [σF] = proj₁ ([F] ⊢Δ [σ])
      [σΠFG] = proj₁ ([ΠFG] ⊢Δ [σ])
      [σt] = proj₁ ([t] ⊢Δ [σ])
      [σu] = proj₁ ([u] ⊢Δ [σ])
      [σG[u]]  = proj₁ ([G[u]] ⊢Δ [σ])
      [σG[u]]′ = irrelevance′ (singleSubstLift G u) [σG[u]]
  in  irrelevanceTerm′ (PE.sym (singleSubstLift G u))
                       [σG[u]]′ [σG[u]]
                       (appTerm [σF] [σG[u]]′ [σΠFG] [σt] [σu] p≈p′)
  ,   (λ [σ′] [σ≡σ′] →
         let [σu′] = convTerm₂ [σF] (proj₁ ([F] ⊢Δ [σ′]))
                               (proj₂ ([F] ⊢Δ [σ]) [σ′] [σ≡σ′])
                               (proj₁ ([u] ⊢Δ [σ′]))
         in  irrelevanceEqTerm′ (PE.sym (singleSubstLift G u))
                                [σG[u]]′ [σG[u]]
                                (app-congTerm [σF] [σG[u]]′ [σΠFG]
                                              (proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′])
                                              [σu] [σu′]
                                              (proj₂ ([u] ⊢Δ [σ]) [σ′] [σ≡σ′])
                                              p≈p′ p≈p′))

-- Application congruence of valid terms.
app-congᵛ : ∀ {F G t u a b l}
            ([Γ] : ⊩ᵛ Γ)
            ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
            ([ΠFG] : Γ ⊩ᵛ⟨ l ⟩ Π p , q ▷ F ▹ G / [Γ])
            ([t≡u] : Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ Π _ , _ ▷ F ▹ G / [Γ] / [ΠFG])
            ([a] : Γ ⊩ᵛ⟨ l ⟩ a ∷ F / [Γ] / [F])
            ([b] : Γ ⊩ᵛ⟨ l ⟩ b ∷ F / [Γ] / [F])
            ([a≡b] : Γ ⊩ᵛ⟨ l ⟩ a ≡ b ∷ F / [Γ] / [F])
          → p ≈ p₁
          → p ≈ p₂
          → Γ ⊩ᵛ⟨ l ⟩ t ∘ p₁ ▷ a ≡ u ∘ p₂ ▷ b ∷ G [ a ] / [Γ]
              / substSΠ {F = F} {G} {a} BΠ! [Γ] [F] [ΠFG] [a]
app-congᵛ {F = F} {G} {a = a} [Γ] [F] [ΠFG] [t≡u] [a] [b] [a≡b] p≈p₁ p≈p₂ ⊢Δ [σ] =
  let [σF] = proj₁ ([F] ⊢Δ [σ])
      [G[a]]  = proj₁ (substSΠ {F = F} {G} {a} BΠ! [Γ] [F] [ΠFG] [a] ⊢Δ [σ])
      [G[a]]′ = irrelevance′ (singleSubstLift G a) [G[a]]
      [σΠFG] = proj₁ ([ΠFG] ⊢Δ [σ])
      [σa] = proj₁ ([a] ⊢Δ [σ])
      [σb] = proj₁ ([b] ⊢Δ [σ])
  in  irrelevanceEqTerm′ (PE.sym (singleSubstLift G a)) [G[a]]′ [G[a]]
                         (app-congTerm [σF] [G[a]]′ [σΠFG] ([t≡u] ⊢Δ [σ])
                                       [σa] [σb] ([a≡b] ⊢Δ [σ]) p≈p₁ p≈p₂)
