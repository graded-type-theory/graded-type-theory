------------------------------------------------------------------------
-- "Equational" reasoning combinators for the abstract machine reduction
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Mode
open import Graded.Usage.Restrictions
open import Definition.Typed.Variant
open import Graded.Usage.Restrictions.Natrec

module Graded.Heap.Reduction.Reasoning
  {a a′} {M : Set a} {Mode : Set a′}
  {𝕄 : Modality M}
  {𝐌 : IsMode Mode 𝕄}
  (type-variant : Type-variant)
  (UR : Usage-restrictions 𝕄 𝐌)
  (open Usage-restrictions UR)
  (factoring-nr :
    ⦃ has-nr : Nr-available ⦄ →
    Is-factoring-nr M (Natrec-mode-Has-nr 𝕄 has-nr))
  (∣ε∣ : M)
  where

open import Graded.Heap.Untyped type-variant UR factoring-nr ∣ε∣
open import Graded.Heap.Reduction type-variant UR factoring-nr ∣ε∣
open import Graded.Heap.Reduction.Properties type-variant UR factoring-nr ∣ε∣

open import Tools.Function
open import Tools.Nat
open import Tools.PropositionalEquality

private variable
  m n k : Nat
  s′ s″ : State _ _ _

infix  -1 finally
infixr -2 step-⇒ₑ step-⇾ₑ step-⇾ₑ* step-⇒ᵥ step-⇒ₙ step-⇾ step-⇾*
          step-↠ step-↠* step-≡ step-≡′ _≡⟨⟩↠_

------------------------------------------------------------------------
-- Combinators for reductions

-- A single step with ⇒ₑ

step-⇒ₑ : ∀ s → s′ ↠* s″ → s ⇒ₑ s′ → s ↠* s″
step-⇒ₑ _ d d′ = ⇾ₑ (⇒ₑ d′) ⇨ d

syntax step-⇒ₑ s s′⇒s″ s⇒s′ = s ⇒ₑ⟨ s⇒s′ ⟩ s′⇒s″

{-# INLINE step-⇒ₑ #-}

-- A single step with ⇾ₑ

step-⇾ₑ : (s : State m n k) → s′ ↠* s″ → s ⇾ₑ s′ → s ↠* s″
step-⇾ₑ _ d d′ = ⇾ₑ d′ ⇨ d

syntax step-⇾ₑ s s′⇒s″ s⇒s′ = s ⇾ₑ⟨ s⇒s′ ⟩ s′⇒s″

{-# INLINE step-⇾ₑ #-}

-- Multiple steps with ⇾ₑ

step-⇾ₑ* : (s : State m n k) → s′ ↠* s″ → s ⇾ₑ* s′ → s ↠* s″
step-⇾ₑ* _ d d′ = ↠*-concat (⇾*→↠* (⇾ₑ* d′)) d

syntax step-⇾ₑ* s s′⇒s″ s⇒s′ = s ⇾ₑ*⟨ s⇒s′ ⟩ s′⇒s″

{-# INLINE step-⇾ₑ* #-}

-- A single step with ⇒ᵥ

step-⇒ᵥ : (s : State m n k) → s′ ↠* s″ → s ⇒ᵥ s′ → s ↠* s″
step-⇒ᵥ _ d d′ = ⇒ᵥ d′ ⇨ d

syntax step-⇒ᵥ s s′⇒s″ s⇒s′ = s ⇒ᵥ⟨ s⇒s′ ⟩ s′⇒s″

{-# INLINE step-⇒ᵥ #-}

-- A single step with ⇒ₙ

step-⇒ₙ : ∀ s → s′ ↠* s″ → s ⇒ₙ s′ → s ↠* s″
step-⇒ₙ _ d d′ = ⇒ₙ d′ ⇨ d

syntax step-⇒ₙ s s′⇒s″ s⇒s′ = s ⇒ₙ⟨ s⇒s′ ⟩ s′⇒s″

{-# INLINE step-⇒ₙ #-}

-- A single step with ⇾

step-⇾ : (s : State m n k) → s′ ↠* s″ → s ⇾ s′ → s ↠* s″
step-⇾ _ d d′ = ⇾→↠ d′ ⇨ d

syntax step-⇾ s s′⇒s″ s⇒s′ = s ⇾⟨ s⇒s′ ⟩ s′⇒s″

{-# INLINE step-⇾ #-}

-- Multiple steps with ⇾

step-⇾* : (s : State m n k) → s′ ↠* s″ → s ⇾* s′ → s ↠* s″
step-⇾* _ d d′ = ↠*-concat (⇾*→↠* d′) d

syntax step-⇾* s s′⇒s″ s⇒s′ = s ⇾*⟨ s⇒s′ ⟩ s′⇒s″

{-# INLINE step-⇾* #-}

-- A single step with ↠

step-↠ : (s : State m n k) → s′ ↠* s″ → s ↠ s′ → s ↠* s″
step-↠ _ d d′ = d′ ⇨ d

syntax step-↠ s s′⇒s″ s⇒s′ = s ↠⟨ s⇒s′ ⟩ s′⇒s″

{-# INLINE step-↠ #-}

-- Multiple steps with ↠

step-↠* : (s : State m n k) → s′ ↠* s″ → s ↠* s′ → s ↠* s″
step-↠* _ = flip ↠*-concat

syntax step-↠* s s′⇒s″ s⇒s′ = s ↠*⟨ s⇒s′ ⟩ s′⇒s″

{-# INLINE step-↠* #-}

finally : (s : State m n k) → s ↠* s
finally _ = id

syntax finally s = s ∎

{-# INLINE finally #-}

-- A reasoning step that uses propositional equality.

step-≡ : (s : State m n k) → s′ ↠* s″ → s ≡ s′ → s ↠* s″
step-≡ _ s⇒s′ refl = s⇒s′

syntax step-≡ s s′⇒s″ s≡s′ = s ≡⟨ s≡s′ ⟩↠ s′⇒s″

{-# INLINE step-≡ #-}

-- A reasoning step that uses propositional equality.

step-≡′ :
  (s : State m n k) → s′ ↠* s″ →
  State.heap s ≡ State.heap s′ →
  State.head s ≡ State.head s′ →
  State.env s ≡ State.env s′ →
  State.stack s ≡ State.stack s′ →
  s ↠* s″
step-≡′ {s′ = record{}} record{} s⇒s′ refl refl refl refl = s⇒s′

syntax step-≡′ s s′⇒s″ H≡H′ t≡t′ ρ≡ρ′ S≡S′ = s ≡⟨ H≡H′ ⨾ t≡t′ ⨾ ρ≡ρ′ ⨾ S≡S′ ⟩↠ s′⇒s″

{-# INLINE step-≡′ #-}

-- A reasoning step that uses (Agda's) definitional equality.

_≡⟨⟩↠_ : (s : State m n k) → s ↠* s′ → s ↠* s′
_ ≡⟨⟩↠ t⇒u = t⇒u

{-# INLINE _≡⟨⟩↠_ #-}
