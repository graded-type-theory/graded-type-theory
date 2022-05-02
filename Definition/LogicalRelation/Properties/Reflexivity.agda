{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation
open import Tools.Level
open import Tools.Relation

module Definition.LogicalRelation.Properties.Reflexivity {a ℓ} (M′ : Setoid a ℓ)
                                                         {{eqrel : EqRelSet M′}} where

open Setoid M′ using () renaming (Carrier to M)

open import Definition.Untyped M hiding (_∷_)
import Definition.Untyped.BindingType M′ as BT
open import Definition.Typed M′
open import Definition.Typed.Weakening M′
open import Definition.Typed.Properties M′
open import Definition.LogicalRelation M′

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n

-- Reflexivity of reducible types.
reflEq : ∀ {l A} ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ A ≡ A / [A]
reflEq (Uᵣ′ l′ l< ⊢Γ) = lift PE.refl
reflEq (ℕᵣ D) = red D
reflEq (Emptyᵣ D) = red D
reflEq (Unitᵣ D) = red D
reflEq (ne′ K [ ⊢A , ⊢B , D ] neK K≡K) =
   ne₌ _ [ ⊢A , ⊢B , D ] neK K≡K
reflEq (Bᵣ′ W F G [ ⊢A , ⊢B , D ] ⊢F ⊢G A≡A [F] [G] G-ext) =
   B₌ _ _ W D BT.refl A≡A
      (λ ρ ⊢Δ → reflEq ([F] ρ ⊢Δ))
      (λ ρ ⊢Δ [a] → reflEq ([G] ρ ⊢Δ [a]))
reflEq (emb 0<1 [A]) = reflEq [A]

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

-- Reflexivity of reducible terms.
reflEqTerm : ∀ {l A t} ([A] : Γ ⊩⟨ l ⟩ A)
           → Γ ⊩⟨ l ⟩ t ∷ A / [A]
           → Γ ⊩⟨ l ⟩ t ≡ t ∷ A / [A]
reflEqTerm (Uᵣ′ ⁰ 0<1 ⊢Γ) (Uₜ A d typeA A≡A [A]) =
  Uₜ₌ A A d d typeA typeA A≡A [A] [A] (reflEq [A])
reflEqTerm (ℕᵣ D) (ℕₜ n [ ⊢t , ⊢u , d ] t≡t prop) =
  ℕₜ₌ n n [ ⊢t , ⊢u , d ] [ ⊢t , ⊢u , d ] t≡t
      (reflNatural-prop prop)
reflEqTerm (Emptyᵣ D) (Emptyₜ n [ ⊢t , ⊢u , d ] t≡t prop) =
  Emptyₜ₌ n n [ ⊢t , ⊢u , d ] [ ⊢t , ⊢u , d ] t≡t
    (reflEmpty-prop prop)
reflEqTerm (Unitᵣ D) (Unitₜ n [ ⊢t , ⊢u , d ] prop) =
  Unitₜ₌ ⊢t ⊢t
reflEqTerm (ne′ K D neK K≡K) (neₜ k d (neNfₜ neK₁ ⊢k k≡k)) =
  neₜ₌ k k d d (neNfₜ₌ neK₁ neK₁ k≡k)
reflEqTerm (Bᵣ′ BΠ! F G D ⊢F ⊢G A≡A [F] [G] G-ext) [t]@(Πₜ f d funcF f≡f [f] [f]₁) =
  Πₜ₌ f f d d funcF funcF f≡f [t] [t]
      (λ ρ ⊢Δ [a] → [f] ρ ⊢Δ [a] [a] (reflEqTerm ([F] ρ ⊢Δ) [a]))
reflEqTerm (Bᵣ′ BΣₚ F G D ⊢F ⊢G A≡A [F] [G] G-ext) [t]@(Σₜ p d p≅p prodP ([fstp] , [sndp])) =
  Σₜ₌ p p d d prodP prodP p≅p [t] [t]
      ([fstp] , [fstp] , reflEqTerm ([F] id (wf ⊢F)) [fstp] , reflEqTerm ([G] id (wf ⊢F) [fstp]) [sndp])
reflEqTerm (Bᵣ′ BΣᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) [t]@(Σₜ p d p≅p prodₙ ([p₁] , [p₂])) =
  Σₜ₌ p p d d prodₙ prodₙ p≅p [t] [t]
      ([p₁] , [p₁] , [p₂] , [p₂] ,
        reflEqTerm ([F] id (wf ⊢F)) [p₁] ,
        reflEqTerm ([G] id (wf ⊢F) [p₁]) [p₂])
reflEqTerm (Bᵣ′ BΣᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) [t]@(Σₜ p d p≅p (ne x) p~p) =
  Σₜ₌ p p d d (ne x) (ne x) p≅p [t] [t] p~p
reflEqTerm (emb 0<1 [A]) t = reflEqTerm [A] t
