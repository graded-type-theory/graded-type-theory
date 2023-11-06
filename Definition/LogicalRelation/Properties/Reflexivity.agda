------------------------------------------------------------------------
-- Equality in the logical relation is reflexive
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Properties.Reflexivity
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open import Definition.Untyped M hiding (_∷_; K)
open import Definition.Typed R
open import Definition.Typed.Weakening R
open import Definition.Typed.Properties R
open import Definition.LogicalRelation R

open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n

reflNatural-prop : ∀ {n}
                 → Natural-prop Γ n
                 → [Natural]-prop Γ n n
reflNatural-prop (sucᵣ (ℕₜ n d t≡t prop)) =
  sucᵣ (ℕₜ₌ n n d d t≡t
            (reflNatural-prop prop))
reflNatural-prop zeroᵣ = zeroᵣ
reflNatural-prop (ne (neNfₜ neK ⊢k k≡k)) = ne (neNfₜ₌ neK neK k≡k)

reflEmpty-prop : ∀ {n}
                 → Empty-prop Γ n
                 → [Empty]-prop Γ n n
reflEmpty-prop (ne (neNfₜ neK ⊢k k≡k)) = ne (neNfₜ₌ neK neK k≡k)

reflUnitʷ-prop : ∀ {t}
               → Unit-prop Γ Σᵣ t
               → [Unitʷ]-prop Γ t t
reflUnitʷ-prop starᵣ = starᵣ
reflUnitʷ-prop (ne (neNfₜ neK ⊢k k≡k)) = ne (neNfₜ₌ neK neK k≡k)


-- Reflexivity of reducible types.
reflEq : ∀ {l A} ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ A ≡ A / [A]

-- Reflexivity of reducible terms.
reflEqTerm : ∀ {l A t} ([A] : Γ ⊩⟨ l ⟩ A)
           → Γ ⊩⟨ l ⟩ t ∷ A / [A]
           → Γ ⊩⟨ l ⟩ t ≡ t ∷ A / [A]

reflEq (Uᵣ′ l′ l< ⊢Γ) = PE.refl
reflEq (ℕᵣ D) = red D
reflEq (Emptyᵣ D) = red D
reflEq (Unitᵣ (Unitₜ D _)) = red D
reflEq (ne′ K [ ⊢A , ⊢B , D ] neK K≡K) =
   ne₌ _ [ ⊢A , ⊢B , D ] neK K≡K
reflEq (Bᵣ′ _ _ _ [ _ , _ , D ] _ _ A≡A [F] [G] _ _) =
   B₌ _ _ D A≡A
      (λ ρ ⊢Δ → reflEq ([F] ρ ⊢Δ))
      (λ ρ ⊢Δ [a] → reflEq ([G] ρ ⊢Δ [a]))
reflEq (Idᵣ ⊩A) = record
  { ⇒*Id′             = ⇒*Id
  ; Ty≡Ty′            = reflEq ⊩Ty
  ; lhs≡lhs′          = reflEqTerm ⊩Ty ⊩lhs
  ; rhs≡rhs′          = reflEqTerm ⊩Ty ⊩rhs
  ; lhs≡rhs→lhs′≡rhs′ = idᶠ
  ; lhs′≡rhs′→lhs≡rhs = idᶠ
  }
  where
  open _⊩ₗId_ ⊩A
reflEq (emb 0<1 [A]) = reflEq [A]

reflEqTerm (Uᵣ′ ⁰ 0<1 ⊢Γ) (Uₜ A d typeA A≡A [A]) =
  Uₜ₌ A A d d typeA typeA A≡A [A] [A] (reflEq [A])
reflEqTerm (ℕᵣ D) (ℕₜ n [ ⊢t , ⊢u , d ] t≡t prop) =
  ℕₜ₌ n n [ ⊢t , ⊢u , d ] [ ⊢t , ⊢u , d ] t≡t
      (reflNatural-prop prop)
reflEqTerm (Emptyᵣ D) (Emptyₜ n [ ⊢t , ⊢u , d ] t≡t prop) =
  Emptyₜ₌ n n [ ⊢t , ⊢u , d ] [ ⊢t , ⊢u , d ] t≡t
    (reflEmpty-prop prop)
reflEqTerm (Unitᵣ {s = Σₚ} D) (Unitₜ n [ ⊢t , ⊢u , d ] t≡t prop) =
  Unitₜ₌ ⊢t ⊢t
reflEqTerm (Unitᵣ {s = Σᵣ} D) (Unitₜ n [ ⊢t , ⊢u , d ] t≡t prop) =
  Unitₜ₌ n n [ ⊢t , ⊢u , d ] [ ⊢t , ⊢u , d ]
         t≡t (reflUnitʷ-prop prop)
reflEqTerm (ne′ K D neK K≡K) (neₜ k d (neNfₜ neK₁ ⊢k k≡k)) =
  neₜ₌ k k d d (neNfₜ₌ neK₁ neK₁ k≡k)
reflEqTerm
  (Bᵣ′ BΠ! _ _ _ _ _ _ [F] _ _ _) [t]@(Πₜ f d funcF f≡f [f] _) =
  Πₜ₌ f f d d funcF funcF f≡f [t] [t]
      (λ ρ ⊢Δ [a] → [f] ρ ⊢Δ [a] [a] (reflEqTerm ([F] ρ ⊢Δ) [a]))
reflEqTerm
  (Bᵣ′ BΣₚ _ _ _ ⊢F _ _ [F] [G] _ _)
  [t]@(Σₜ p d p≅p prodP ([fstp] , [sndp])) =
  Σₜ₌ p p d d prodP prodP p≅p [t] [t]
      ([fstp] , [fstp] , reflEqTerm ([F] id (wf ⊢F)) [fstp] , reflEqTerm ([G] id (wf ⊢F) [fstp]) [sndp])
reflEqTerm
  (Bᵣ′ BΣᵣ _ _ _ ⊢F _ _ [F] [G] _ _)
  [t]@(Σₜ p d p≅p prodₙ (PE.refl , [p₁] , [p₂] , PE.refl)) =
  Σₜ₌ p p d d prodₙ prodₙ p≅p [t] [t]
      (PE.refl , PE.refl , [p₁] , [p₁] , [p₂] , [p₂] ,
        reflEqTerm ([F] id (wf ⊢F)) [p₁] ,
        reflEqTerm ([G] id (wf ⊢F) [p₁]) [p₂])
reflEqTerm (Bᵣ′ BΣᵣ _ _ _ _ _ _ _ _ _ _) [t]@(Σₜ p d p≅p (ne x) p~p) =
  Σₜ₌ p p d d (ne x) (ne x) p≅p [t] [t] p~p
reflEqTerm (Idᵣ _) ⊩t =
  ⊩Id≡∷ ⊩t ⊩t
    (case ⊩Id∷-view-inhabited ⊩t of λ where
       (rflᵣ _)     → _
       (ne _ t′~t′) → t′~t′)
reflEqTerm (emb 0<1 [A]) t = reflEqTerm [A] t
