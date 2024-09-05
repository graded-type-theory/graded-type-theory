------------------------------------------------------------------------
-- Typing for heaps, stacks and states
------------------------------------------------------------------------

open import Graded.Modality
open import Definition.Typed.Restrictions
open import Tools.Bool

module Heap.Typed
  {a} {M : Set a} {𝕄 : Modality M}
  (TR : Type-restrictions 𝕄)
  (ℕ-fullred : Bool)
  where

open Type-restrictions TR

open import Definition.Untyped M
open import Definition.Untyped.Properties M
open import Definition.Typed TR
import Graded.Derived.Erased.Untyped 𝕄 as Erased

open import Heap.Untyped 𝕄 type-variant

open import Tools.Fin
open import Tools.Nat
open import Tools.Product
open import Tools.Relation
import Tools.PropositionalEquality as PE

private variable
  m n k : Nat
  Γ Δ : Con Term _
  H : Heap _ _
  E : Env _ _
  e : Elim _
  S : Stack _
  t u v w z s A B B′ C : Term _
  p q q′ r : M
  s′ : Strength

-- Well-formed heaps

data _⊢ʰ_∷_ : (Δ : Con Term k) (H : Heap k m) (Γ : Con Term m) → Set a where
  ε : ⊢ Δ → Δ ⊢ʰ ε ∷ ε
  _∙_ : Δ ⊢ʰ H ∷ Γ → Δ ⊢ wk E t [ H ]ₕ ∷ A [ H ]ₕ → Δ ⊢ʰ H ∙ (p , t , E) ∷ Γ ∙ A
  _∙●_ : Δ ⊢ʰ H ∷ Γ → Γ ⊢ A → Δ ∙ A [ H ]ₕ ⊢ʰ H ∙● ∷ Γ ∙ A

-- Well-formed eliminators

data _⨾_⊢ᵉ_⟨_⟩∷_↝_ (Δ : Con Term k) (H : Heap k m) :
                  (e : Elim m) (t : Term m) (A B : Term k) → Set a where
  ∘ₑ : Δ ⊢ wk E u [ H ]ₕ ∷ A
     → Δ ∙ A ⊢ B
     → Δ ⨾ H ⊢ᵉ ∘ₑ p u E ⟨ t ⟩∷ Π p , q ▷ A ▹ B ↝ B [ wk E u [ H ]ₕ ]₀
  fstₑ : Δ ⊢ A
       → Δ ∙ A ⊢ B
       → Δ ⨾ H ⊢ᵉ fstₑ p ⟨ t ⟩∷ Σˢ p , q ▷ A ▹ B ↝ A
  sndₑ : Δ ⊢ A
       → Δ ∙ A ⊢ B
       → Δ ⨾ H ⊢ᵉ sndₑ p ⟨ t ⟩∷ Σˢ p , q ▷ A ▹ B ↝ B [ fst p t [ H ]ₕ ]₀
  prodrecₑ : Δ ∙ B ∙ C ⊢ wk (liftn E 2) u [ H ]⇑²ₕ ∷ (wk (lift E) A [ H ]⇑ₕ [ prodʷ p (var x1) (var x0) ]↑²)
           → Δ ∙ Σʷ p , q′ ▷ B ▹ C ⊢ wk (lift E) A [ H ]⇑ₕ
           → Δ ⨾ H ⊢ᵉ prodrecₑ r p q A u E ⟨ t ⟩∷ Σʷ p , q′ ▷ B ▹ C ↝ (wk (lift E) A [ H ]⇑ₕ [ t [ H ]ₕ ]₀)
  natrecₑ : Δ ⊢ wk E z [ H ]ₕ ∷ wk (lift E) A [ H ]⇑ₕ [ zero ]₀
          → Δ ∙ ℕ ∙ wk (lift E) A [ H ]⇑ₕ ⊢ wk (liftn E 2) s [ H ]⇑²ₕ ∷ wk (lift E) A [ H ]⇑ₕ [ suc (var x1) ]↑²
          → Δ ∙ ℕ ⊢ wk (lift E) A [ H ]⇑ₕ
          → Δ ⨾ H ⊢ᵉ natrecₑ p q r A z s E ⟨ t ⟩∷ ℕ ↝ wk (lift E) A [ H ]⇑ₕ [ t [ H ]ₕ ]₀
  unitrecₑ : Δ ⊢ wk E u [ H ]ₕ ∷ wk (lift E) A [ H ]⇑ₕ [ starʷ ]₀
           → Δ ∙ Unitʷ ⊢ wk (lift E) A [ H ]⇑ₕ
           → ¬ Unitʷ-η
           → Δ ⨾ H ⊢ᵉ unitrecₑ p q A u E ⟨ t ⟩∷ Unitʷ ↝ (wk (lift E) A [ H ]⇑ₕ [ t [ H ]ₕ ]₀)
  Jₑ : let A′ = wk E A [ H ]ₕ
           B′ = wk (liftn E 2) B [ H ]⇑²ₕ
           t′ = wk E t [ H ]ₕ
           u′ = wk E u [ H ]ₕ
           v′ = wk E v [ H ]ₕ
       in  Δ ⊢ u′ ∷ B′ [ t′ , rfl ]₁₀ →
           Δ ∙ A′ ∙ Id (wk1 A′) (wk1 t′) (var x0) ⊢ B′ →
           Δ ⨾ H ⊢ᵉ Jₑ p q A t B u v E ⟨ w ⟩∷ wk E (Id A t v) [ H ]ₕ
             ↝ B′ [ v′ , w [ H ]ₕ ]₁₀
  Kₑ : Δ ⊢ wk E u [ H ]ₕ ∷ wk (lift E) B [ H ]⇑ₕ [ rfl ]₀
     → Δ ∙ wk E (Id A t t) [ H ]ₕ ⊢ wk (lift E) B [ H ]⇑ₕ
     → K-allowed
     → Δ ⨾ H ⊢ᵉ Kₑ p A t B u E ⟨ v ⟩∷ wk E (Id A t t) [ H ]ₕ ↝ wk (lift E) B [ H ]⇑ₕ [ v [ H ]ₕ ]₀
  []-congₑ : []-cong-allowed s′
           → let open Erased s′
             in  Δ ⨾ H ⊢ᵉ []-congₑ s′ A t u E ⟨ v ⟩∷ wk E (Id A t u) [ H ]ₕ ↝ (wk E (Id (Erased A) ([ t ]) ([ u ])) [ H ]ₕ)
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
Δ ⨾ Γ ⊢ ⟨ H , t , E , S ⟩ ∷ A =
  ∃ λ B → (Δ ⊢ʰ H ∷ Γ) × (Δ ⊢ wk E t [ H ]ₕ ∷ B) × Δ ⨾ H ⊢ S ⟨ wk E t ⟩∷ B ↝ A
