------------------------------------------------------------------------
-- Properties of well-formed heaps as substitutions
------------------------------------------------------------------------

open import Graded.Modality
open import Definition.Typed.Restrictions
open import Tools.Bool

module Heap.Typed.Substitution
  {a} {M : Set a} {𝕄 : Modality M}
  (TR : Type-restrictions 𝕄)
  (ℕ-fullred : Bool)
  where

open import Definition.Untyped M
open import Definition.Untyped.Properties M
open import Definition.Typed TR
open import Definition.Typed.Consequences.Substitution TR

open import Heap.Typed TR ℕ-fullred
open import Heap.Untyped 𝕄
open import Heap.Untyped.Properties 𝕄

open import Tools.Function
open import Tools.Product
open import Tools.Reasoning.PropositionalEquality
import Tools.PropositionalEquality as PE

private variable
  Γ : Con Term _
  H H′ : Heap _
  E : Env _ _
  t u A B : Term _
  y : Ptr _
  c : Closure _ _
  p : M
  e : Elim _
  S : Stack _
  σ : Subst _ _

opaque

  -- A well-formed heap is a well-formed substitution

  ⊢ʰ→⊢ˢ : Γ ⊢ʰ H → ε ⊢ˢ toSubstₕ H ∷ Γ
  ⊢ʰ→⊢ˢ ε = id
  ⊢ʰ→⊢ˢ (⊢H ∙ ⊢t) = ⊢ʰ→⊢ˢ ⊢H , ⊢t

opaque

  -- A well-formed type applied to a well-formed heap (as a substitution)
  -- is well-formed

  substHeap : Γ ⊢ʰ H → Γ ⊢ A → ε ⊢ A [ H ]ₕ
  substHeap ⊢H ⊢A =
    substitution ⊢A (⊢ʰ→⊢ˢ ⊢H) ε

opaque

  -- A well-formed term applied to a well-formed heap (as a substitution)
  -- is well-formed

  substHeapTerm : Γ ⊢ʰ H → Γ ⊢ t ∷ A → ε ⊢ t [ H ]ₕ ∷ A [ H ]ₕ
  substHeapTerm ⊢H ⊢t =
    substitutionTerm ⊢t (⊢ʰ→⊢ˢ ⊢H) ε

opaque

  -- A well-formed type equality applied to a well-formed heap
  -- (as a substitution) is well-formed

  substHeapEq : Γ ⊢ʰ H → Γ ⊢ A ≡ B → ε ⊢ A [ H ]ₕ ≡ B [ H ]ₕ
  substHeapEq ⊢H ⊢A≡B =
    substitutionEq ⊢A≡B (substRefl (⊢ʰ→⊢ˢ ⊢H)) ε

opaque

  -- A well-formed term equality  applied to a well-formed heap
  -- (as a substitution) is well-formed

  substHeapEqTerm : Γ ⊢ʰ H → Γ ⊢ t ≡ u ∷ A
                  → ε ⊢ t [ H ]ₕ ≡ u [ H ]ₕ ∷ A [ H ]ₕ
  substHeapEqTerm ⊢H ⊢t≡u =
    substitutionEqTerm ⊢t≡u (substRefl (⊢ʰ→⊢ˢ ⊢H)) ε

opaque

  -- Applying a well-formed heap as a substitution to a reduction

  substHeapRedTerm : Γ ⊢ʰ H → Γ ⊢ t ⇒ u ∷ A → ε ⊢ t [ H ]ₕ ⇒ u [ H ]ₕ ∷ A [ H ]ₕ
  substHeapRedTerm ⊢H d =
    substitutionRedTerm d (⊢ʰ→⊢ˢ ⊢H) ε
