------------------------------------------------------------------------
-- Typing for heaps, stacks and states
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.Restrictions
open import Tools.Bool

module Graded.Heap.Typed
  {a} {M : Set a} {𝕄 : Modality M}
  (UR : Usage-restrictions 𝕄)
  (TR : Type-restrictions 𝕄)
  (ℕ-fullred : Bool)
  where

open Type-restrictions TR

open import Definition.Untyped M
open import Definition.Typed TR
import Graded.Derived.Erased.Untyped 𝕄 as Erased

open import Graded.Heap.Untyped type-variant UR

open import Tools.Fin
open import Tools.Nat
open import Tools.Product
open import Tools.Relation
import Tools.PropositionalEquality as PE

private variable
  m n k : Nat
  Γ Δ : Con Term _
  H : Heap _ _
  ρ : Wk _ _
  e : Elim _
  S : Stack _
  t u v w z s A B B′ C : Term _
  p q q′ r : M
  s′ : Strength

-- Well-formed heaps

data _⊢ʰ_∷_ : (Δ : Con Term k) (H : Heap k m) (Γ : Con Term m) → Set a where
  ε : ε ⊢ʰ ε ∷ ε
  _∙_ : Δ ⊢ʰ H ∷ Γ → Δ ⊢ wk ρ t [ H ]ₕ ∷ A [ H ]ₕ → Δ ⊢ʰ H ∙ (p , t , ρ) ∷ Γ ∙ A
  _∙●_ : Δ ⊢ʰ H ∷ Γ → Γ ⊢ A → Δ ∙ A [ H ]ₕ ⊢ʰ H ∙● ∷ Γ ∙ A

-- Well-formed eliminators

data _⨾_⊢ᵉ_⟨_⟩∷_↝_ (Δ : Con Term k) (H : Heap k m) :
                  (e : Elim m) (t : Term m) (A B : Term k) → Set a where
  ∘ₑ : Δ ⊢ wk ρ u [ H ]ₕ ∷ A
     → Δ ∙ A ⊢ B
     → Δ ⨾ H ⊢ᵉ ∘ₑ p u ρ ⟨ t ⟩∷ Π p , q ▷ A ▹ B ↝ B [ wk ρ u [ H ]ₕ ]₀
  fstₑ : Δ ⊢ A
       → Δ ∙ A ⊢ B
       → Δ ⨾ H ⊢ᵉ fstₑ p ⟨ t ⟩∷ Σˢ p , q ▷ A ▹ B ↝ A
  sndₑ : Δ ⊢ A
       → Δ ∙ A ⊢ B
       → Δ ⨾ H ⊢ᵉ sndₑ p ⟨ t ⟩∷ Σˢ p , q ▷ A ▹ B ↝ B [ fst p t [ H ]ₕ ]₀
  prodrecₑ : Δ ∙ B ∙ C ⊢ wk (liftn ρ 2) u [ H ]⇑²ₕ ∷ (wk (lift ρ) A [ H ]⇑ₕ [ prodʷ p (var x1) (var x0) ]↑²)
           → Δ ∙ Σʷ p , q′ ▷ B ▹ C ⊢ wk (lift ρ) A [ H ]⇑ₕ
           → Δ ⨾ H ⊢ᵉ prodrecₑ r p q A u ρ ⟨ t ⟩∷ Σʷ p , q′ ▷ B ▹ C ↝ (wk (lift ρ) A [ H ]⇑ₕ [ t [ H ]ₕ ]₀)
  natrecₑ : Δ ⊢ wk ρ z [ H ]ₕ ∷ wk (lift ρ) A [ H ]⇑ₕ [ zero ]₀
          → Δ ∙ ℕ ∙ wk (lift ρ) A [ H ]⇑ₕ ⊢ wk (liftn ρ 2) s [ H ]⇑²ₕ ∷ wk (lift ρ) A [ H ]⇑ₕ [ suc (var x1) ]↑²
          → Δ ∙ ℕ ⊢ wk (lift ρ) A [ H ]⇑ₕ
          → Δ ⨾ H ⊢ᵉ natrecₑ p q r A z s ρ ⟨ t ⟩∷ ℕ ↝ wk (lift ρ) A [ H ]⇑ₕ [ t [ H ]ₕ ]₀
  unitrecₑ : Δ ⊢ wk ρ u [ H ]ₕ ∷ wk (lift ρ) A [ H ]⇑ₕ [ starʷ ]₀
           → Δ ∙ Unitʷ ⊢ wk (lift ρ) A [ H ]⇑ₕ
           → ¬ Unitʷ-η
           → Δ ⨾ H ⊢ᵉ unitrecₑ p q A u ρ ⟨ t ⟩∷ Unitʷ ↝ (wk (lift ρ) A [ H ]⇑ₕ [ t [ H ]ₕ ]₀)
  emptyrecₑ : Δ ⊢ wk ρ A [ H ]ₕ
            → Δ ⨾ H ⊢ᵉ emptyrecₑ p A ρ ⟨ t ⟩∷ Empty ↝ wk ρ A [ H ]ₕ
  Jₑ : let A′ = wk ρ A [ H ]ₕ
           B′ = wk (liftn ρ 2) B [ H ]⇑²ₕ
           t′ = wk ρ t [ H ]ₕ
           u′ = wk ρ u [ H ]ₕ
           v′ = wk ρ v [ H ]ₕ
       in  Δ ⊢ u′ ∷ B′ [ t′ , rfl ]₁₀ →
           Δ ∙ A′ ∙ Id (wk1 A′) (wk1 t′) (var x0) ⊢ B′ →
           Δ ⨾ H ⊢ᵉ Jₑ p q A t B u v ρ ⟨ w ⟩∷ wk ρ (Id A t v) [ H ]ₕ
             ↝ B′ [ v′ , w [ H ]ₕ ]₁₀
  Kₑ : Δ ⊢ wk ρ u [ H ]ₕ ∷ wk (lift ρ) B [ H ]⇑ₕ [ rfl ]₀
     → Δ ∙ wk ρ (Id A t t) [ H ]ₕ ⊢ wk (lift ρ) B [ H ]⇑ₕ
     → K-allowed
     → Δ ⨾ H ⊢ᵉ Kₑ p A t B u ρ ⟨ v ⟩∷ wk ρ (Id A t t) [ H ]ₕ ↝ wk (lift ρ) B [ H ]⇑ₕ [ v [ H ]ₕ ]₀
  []-congₑ : []-cong-allowed s′
           → let open Erased s′
             in  Δ ⨾ H ⊢ᵉ []-congₑ s′ A t u ρ ⟨ v ⟩∷ wk ρ (Id A t u) [ H ]ₕ ↝ (wk ρ (Id (Erased A) ([ t ]) ([ u ])) [ H ]ₕ)
  sucₑ : ⦃ T ℕ-fullred ⦄ → Δ ⨾ H ⊢ᵉ sucₑ ⟨ t ⟩∷ ℕ ↝ ℕ
  conv : Δ ⨾ H ⊢ᵉ e ⟨ t ⟩∷ A ↝ B
       → Δ ⊢ B ≡ B′
       → Δ ⨾ H ⊢ᵉ e ⟨ t ⟩∷ A ↝ B′

-- Well-formed stacks

data _⨾_⊢_⟨_⟩∷_↝_ (Δ : Con Term k) (H : Heap k m) : (S : Stack m) (t : Term m) (A B : Term k) → Set a where
  ε : Δ ⨾ H ⊢ ε ⟨ t ⟩∷ A ↝ A
  _∙_ : (⊢e : Δ ⨾ H ⊢ᵉ e ⟨ t ⟩∷ A ↝ B)
      → (⊢S : Δ ⨾ H ⊢ S ⟨ ⦅ e ⦆ᵉ t ⟩∷ B ↝ C)
      → Δ ⨾ H ⊢ e ∙ S ⟨ t ⟩∷ A ↝ C

-- Well-formed evaluation states

_⨾_⊢_∷_ : (Δ : Con Term k) (Γ : Con Term m) (s : State k m n) (A : Term k) → Set a
Δ ⨾ Γ ⊢ ⟨ H , t , ρ , S ⟩ ∷ A =
  ∃ λ B → (Δ ⊢ʰ H ∷ Γ) × (Δ ⊢ wk ρ t [ H ]ₕ ∷ B) × Δ ⨾ H ⊢ S ⟨ wk ρ t ⟩∷ B ↝ A
