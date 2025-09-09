------------------------------------------------------------------------
-- Typing for heaps, stacks and states
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.Restrictions
open import Graded.Usage.Restrictions.Natrec

module Graded.Heap.Typed
  {a} {M : Set a} {𝕄 : Modality M}
  (UR : Usage-restrictions 𝕄)
  (TR : Type-restrictions 𝕄)
  (open Usage-restrictions UR)
  (factoring-nr :
    ⦃ has-nr : Nr-available ⦄ →
    Is-factoring-nr M (Natrec-mode-Has-nr 𝕄 has-nr))
  where

open Type-restrictions TR

open import Definition.Untyped M
import Definition.Untyped.Erased 𝕄 as Erased
open import Definition.Typed TR

open import Graded.Heap.Untyped type-variant UR factoring-nr

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
  c : Cont _
  S : Stack _
  t u v w z s A B B′ C : Term _
  p q q′ r : M
  s′ : Strength
  l : Universe-level

-- Well-formed heaps

data _⊢ʰ_∷_ : (Δ : Con Term k) (H : Heap k m) (Γ : Con Term m) → Set a where
  ε : ε ⊢ʰ ε ∷ ε
  _∙_ : Δ ⊢ʰ H ∷ Γ → ε » Δ ⊢ wk ρ t [ H ]ₕ ∷ A [ H ]ₕ →
        Δ ⊢ʰ H ∙ (p , t , ρ) ∷ Γ ∙ A
  _∙●_ : Δ ⊢ʰ H ∷ Γ → ε » Γ ⊢ A → Δ ∙ A [ H ]ₕ ⊢ʰ H ∙● ∷ Γ ∙ A

-- Well-formed continuations

data _⨾_⊢ᶜ_⟨_⟩∷_↝_ (Δ : Con Term k) (H : Heap k m) :
                  (c : Cont m) (t : Term m) (A B : Term k) → Set a where
  ∘ₑ : ε » Δ ⊢ wk ρ u [ H ]ₕ ∷ A
     → ε » Δ ∙ A ⊢ B
     → Δ ⨾ H ⊢ᶜ ∘ₑ p u ρ ⟨ t ⟩∷ Π p , q ▷ A ▹ B ↝ B [ wk ρ u [ H ]ₕ ]₀
  fstₑ : ε » Δ ∙ A ⊢ B
       → Δ ⨾ H ⊢ᶜ fstₑ p ⟨ t ⟩∷ Σˢ p , q ▷ A ▹ B ↝ A
  sndₑ : ε » Δ ∙ A ⊢ B
       → Δ ⨾ H ⊢ᶜ sndₑ p ⟨ t ⟩∷ Σˢ p , q ▷ A ▹ B ↝ B [ fst p t [ H ]ₕ ]₀
  prodrecₑ : ε » Δ ∙ B ∙ C ⊢ wk (liftn ρ 2) u [ H ]⇑²ₕ ∷
               (wk (lift ρ) A [ H ]⇑ₕ [ prodʷ p (var x1) (var x0) ]↑²)
           → ε » Δ ∙ Σʷ p , q′ ▷ B ▹ C ⊢ wk (lift ρ) A [ H ]⇑ₕ
           → Δ ⨾ H ⊢ᶜ prodrecₑ r p q A u ρ ⟨ t ⟩∷ Σʷ p , q′ ▷ B ▹ C ↝ (wk (lift ρ) A [ H ]⇑ₕ [ t [ H ]ₕ ]₀)
  natrecₑ : ε » Δ ⊢ wk ρ z [ H ]ₕ ∷ wk (lift ρ) A [ H ]⇑ₕ [ zero ]₀
          → ε » Δ ∙ ℕ ∙ wk (lift ρ) A [ H ]⇑ₕ ⊢
              wk (liftn ρ 2) s [ H ]⇑²ₕ ∷
              wk (lift ρ) A [ H ]⇑ₕ [ suc (var x1) ]↑²
          → Δ ⨾ H ⊢ᶜ natrecₑ p q r A z s ρ ⟨ t ⟩∷ ℕ ↝ wk (lift ρ) A [ H ]⇑ₕ [ t [ H ]ₕ ]₀
  unitrecₑ : ε » Δ ⊢ wk ρ u [ H ]ₕ ∷ wk (lift ρ) A [ H ]⇑ₕ [ starʷ l ]₀
           → ε » Δ ∙ Unitʷ l ⊢ wk (lift ρ) A [ H ]⇑ₕ
           → ¬ Unitʷ-η
           → Δ ⨾ H ⊢ᶜ unitrecₑ l p q A u ρ ⟨ t ⟩∷ Unitʷ l ↝
               wk (lift ρ) A [ H ]⇑ₕ [ t [ H ]ₕ ]₀
  emptyrecₑ : ε » Δ ⊢ wk ρ A [ H ]ₕ
            → Δ ⨾ H ⊢ᶜ emptyrecₑ p A ρ ⟨ t ⟩∷ Empty ↝ wk ρ A [ H ]ₕ
  Jₑ : let A′ = wk ρ A [ H ]ₕ
           B′ = wk (liftn ρ 2) B [ H ]⇑²ₕ
           t′ = wk ρ t [ H ]ₕ
           u′ = wk ρ u [ H ]ₕ
           v′ = wk ρ v [ H ]ₕ
       in  ε » Δ ⊢ u′ ∷ B′ [ t′ , rfl ]₁₀ →
           ε » Δ ∙ A′ ∙ Id (wk1 A′) (wk1 t′) (var x0) ⊢ B′ →
           Δ ⨾ H ⊢ᶜ Jₑ p q A t B u v ρ ⟨ w ⟩∷ wk ρ (Id A t v) [ H ]ₕ
             ↝ B′ [ v′ , w [ H ]ₕ ]₁₀
  Kₑ : ε » Δ ⊢ wk ρ u [ H ]ₕ ∷ wk (lift ρ) B [ H ]⇑ₕ [ rfl ]₀
     → ε » Δ ∙ wk ρ (Id A t t) [ H ]ₕ ⊢ wk (lift ρ) B [ H ]⇑ₕ
     → K-allowed
     → Δ ⨾ H ⊢ᶜ Kₑ p A t B u ρ ⟨ v ⟩∷ wk ρ (Id A t t) [ H ]ₕ ↝ wk (lift ρ) B [ H ]⇑ₕ [ v [ H ]ₕ ]₀
  []-congₑ : []-cong-allowed s′
           → let open Erased s′
             in  Δ ⨾ H ⊢ᶜ []-congₑ s′ A t u ρ ⟨ v ⟩∷ wk ρ (Id A t u) [ H ]ₕ ↝ (wk ρ (Id (Erased A) ([ t ]) ([ u ])) [ H ]ₕ)
  conv : Δ ⨾ H ⊢ᶜ c ⟨ t ⟩∷ A ↝ B
       → ε » Δ ⊢ B ≡ B′
       → Δ ⨾ H ⊢ᶜ c ⟨ t ⟩∷ A ↝ B′

-- Well-formed stacks

data _⨾_⊢_⟨_⟩∷_↝_ (Δ : Con Term k) (H : Heap k m) : (S : Stack m) (t : Term m) (A B : Term k) → Set a where
  ε : Δ ⨾ H ⊢ ε ⟨ t ⟩∷ A ↝ A
  _∙_ : (⊢c : Δ ⨾ H ⊢ᶜ c ⟨ t ⟩∷ A ↝ B)
      → (⊢S : Δ ⨾ H ⊢ S ⟨ ⦅ c ⦆ᶜ t ⟩∷ B ↝ C)
      → Δ ⨾ H ⊢ c ∙ S ⟨ t ⟩∷ A ↝ C

-- Well-formed evaluation states

data _⊢ₛ_∷_ {m n} (Δ : Con Term k) : (s : State k m n) (A : Term k) → Set a where
  ⊢ₛ : Δ ⊢ʰ H ∷ Γ
     → ε » Δ ⊢ wk ρ t [ H ]ₕ ∷ B → Δ ⨾ H ⊢ S ⟨ wk ρ t ⟩∷ B ↝ A
     → Δ ⊢ₛ ⟨ H , t , ρ , S ⟩ ∷ A
