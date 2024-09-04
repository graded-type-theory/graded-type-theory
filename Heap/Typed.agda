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

open import Heap.Untyped 𝕄

open import Tools.Fin
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private variable
  m n : Nat
  Γ : Con Term _
  H : Heap _
  E : Env _ _
  e : Elim _
  S : Stack _
  t u v w z s A B B′ C : Term _
  p q q′ r : M
  s′ : Strength

-- Well-formed heap

data _⊢ʰ_ : (Γ : Con Term m) (H : Heap m) → Set a where
  ε : ε ⊢ʰ ε
  _∙_ : Γ ⊢ʰ H
      → ε ⊢ wk E t [ H ]ₕ ∷ A [ H ]ₕ
      → Γ ∙ A ⊢ʰ H ∙ (p , t , E)

-- Well-formed eliminator

data _⊢ᵉ_∷_∷_↝_ (H : Heap m) : (e : Elim m) (t : Term m) (A B : Term 0) → Set a where
  ∘ₑ : ε ⊢ wk E u [ H ]ₕ ∷ A
     → ε ∙ A ⊢ B
     → H ⊢ᵉ ∘ₑ p u E ∷ t ∷ (Π p , q ▷ A ▹ B) ↝ B [ wk E u [ H ]ₕ ]₀
  fstₑ : ε ⊢ A
       → ε ∙ A ⊢ B
       → H ⊢ᵉ fstₑ p ∷ t ∷ Σˢ p , q ▷ A ▹ B ↝ A
  sndₑ : ε ⊢ A
       → ε ∙ A ⊢ B
       → H ⊢ᵉ sndₑ p ∷ t ∷ Σˢ p , q ▷ A ▹ B ↝ B [ fst p t [ H ]ₕ ]₀
  prodrecₑ : ε ∙ B ∙ C ⊢ wk (liftn E 2) u [ H ]⇑²ₕ ∷ (wk (lift E) A [ H ]⇑ₕ [ prodʷ p (var x1) (var x0) ]↑²)
           → ε ∙ Σʷ p , q′ ▷ B ▹ C ⊢ wk (lift E) A [ H ]⇑ₕ
           → H ⊢ᵉ prodrecₑ r p q A u E ∷ t ∷ Σʷ p , q′ ▷ B ▹ C ↝ (wk (lift E) A [ H ]⇑ₕ [ t [ H ]ₕ ]₀)
  natrecₑ : ε ⊢ wk E z [ H ]ₕ ∷ wk (lift E) A [ H ]⇑ₕ [ zero ]₀
          → ε ∙ ℕ ∙ wk (lift E) A [ H ]⇑ₕ ⊢ wk (liftn E 2) s [ H ]⇑²ₕ ∷ wk (lift E) A [ H ]⇑ₕ [ suc (var x1) ]↑²
          → ε ∙ ℕ ⊢ wk (lift E) A [ H ]⇑ₕ
          → H ⊢ᵉ natrecₑ p q r A z s E ∷ t ∷ ℕ ↝ wk (lift E) A [ H ]⇑ₕ [ t [ H ]ₕ ]₀
  unitrecₑ : ε ⊢ wk E u [ H ]ₕ ∷ wk (lift E) A [ H ]⇑ₕ [ starʷ ]₀
           → ε ∙ Unitʷ ⊢ wk (lift E) A [ H ]⇑ₕ
           → H ⊢ᵉ unitrecₑ p q A u E ∷ t ∷ Unitʷ ↝ (wk (lift E) A [ H ]⇑ₕ [ t [ H ]ₕ ]₀)
  Jₑ : let A′ = wk E A [ H ]ₕ
           B′ = wk (liftn E 2) B [ H ]⇑²ₕ
           t′ = wk E t [ H ]ₕ
           u′ = wk E u [ H ]ₕ
           v′ = wk E v [ H ]ₕ
       in  ε ⊢ u′ ∷ B′ [ t′ , rfl ]₁₀ →
           ε ∙ A′ ∙ Id (wk1 A′) (wk1 t′) (var x0) ⊢ B′ →
           H ⊢ᵉ Jₑ p q A t B u v E ∷ w ∷ wk E (Id A t v) [ H ]ₕ
             ↝ B′ [ v′ , w [ H ]ₕ ]₁₀
  Kₑ : ε ⊢ wk E u [ H ]ₕ ∷ wk (lift E) B [ H ]⇑ₕ [ rfl ]₀
     → ε ∙ wk E (Id A t t) [ H ]ₕ ⊢ wk (lift E) B [ H ]⇑ₕ
     → K-allowed
     → H ⊢ᵉ Kₑ p A t B u E ∷ v ∷ wk E (Id A t t) [ H ]ₕ ↝ wk (lift E) B [ H ]⇑ₕ [ v [ H ]ₕ ]₀
  []-congₑ : []-cong-allowed s′
           → let open Erased s′
             in  H ⊢ᵉ []-congₑ s′ A t u E ∷ v ∷ wk E (Id A t u) [ H ]ₕ ↝ (wk E (Id (Erased A) ([ t ]) ([ u ])) [ H ]ₕ)
  sucₑ : ⦃ T ℕ-fullred ⦄ → H ⊢ᵉ sucₑ ∷ t ∷ ℕ ↝ ℕ
  conv : H ⊢ᵉ e ∷ t ∷ A ↝ B
       → ε ⊢ B ≡ B′
       → H ⊢ᵉ e ∷ t ∷ A ↝ B′

-- Well-formed stack

data _⊢_∷_∷_↝_ (H : Heap m) : (S : Stack m) (t : Term m) (A B : Term 0) → Set a where
  ε : H ⊢ ε ∷ t ∷ A ↝ A
  _∙_ : (⊢e : H ⊢ᵉ e ∷ t ∷ A ↝ B)
      → (⊢S : H ⊢ S ∷ ⦅ e ⦆ᵉ t ∷ B ↝ C)
      → H ⊢ e ∙ S ∷ t ∷ A ↝ C

-- Well-formed evaluation state

_⊢ₛ_∷_ : (Γ : Con Term m) (s : State m n) (A : Term 0) → Set a
Γ ⊢ₛ ⟨ H , t , E , S ⟩ ∷ A =
  ∃ λ B → (Γ ⊢ʰ H) × (ε ⊢ wk E t [ H ]ₕ ∷ B) × (H ⊢ S ∷ wk E t ∷ B ↝ A)

opaque

  -- Typing of the initial state

  ⊢initial : ε ⊢ t ∷ A → ε ⊢ₛ initial t ∷ A
  ⊢initial {t} ⊢t =
    _ , ε , PE.subst (ε ⊢_∷ _)
      (PE.sym (PE.trans (subst-id (wk id t)) (wk-id t))) ⊢t , ε
