------------------------------------------------------------------------
-- Properties of well-formed heaps as substitutions
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.Restrictions
open import Tools.Bool

module Heap.Typed.Substitution
  {a} {M : Set a} {𝕄 : Modality M}
  (UR : Usage-restrictions 𝕄)
  (TR : Type-restrictions 𝕄)
  (ℕ-fullred : Bool)
  where

open Type-restrictions TR

open import Definition.Untyped M
open import Definition.Untyped.Properties M
open import Definition.Typed TR
open import Definition.Typed.Properties TR
open import Definition.Typed.Consequences.Substitution TR

open import Heap.Typed UR TR ℕ-fullred
open import Heap.Untyped type-variant UR

import Tools.PropositionalEquality as PE

private variable
  Γ Δ : Con Term _
  H H′ : Heap _ _
  ρ : Wk _ _
  t u A B : Term _
  y : Ptr _
  c : Entry _ _
  p : M
  e : Elim _
  S : Stack _
  σ : Subst _ _

opaque mutual

  -- A well-formed heap is a well-formed substitution

  ⊢ʰ→⊢ˢ : Δ ⊢ʰ H ∷ Γ → Δ ⊢ˢ toSubstₕ H ∷ Γ
  ⊢ʰ→⊢ˢ ε = id
  ⊢ʰ→⊢ˢ (⊢H ∙ ⊢t) =
    ⊢ʰ→⊢ˢ ⊢H , ⊢t
  ⊢ʰ→⊢ˢ (_∙●_ {Δ} {H} {A} ⊢H ⊢A) =
    let ⊢σ = ⊢ʰ→⊢ˢ ⊢H
        ⊢Δ = wfHeap ⊢H
        ⊢σA = substitution ⊢A ⊢σ ⊢Δ
    in    wk1Subst′ (wf ⊢A) ⊢σA ⊢σ
        , var (⊢Δ ∙ ⊢σA) (PE.subst (y0 ∷_∈ Δ ∙ A [ H ]ₕ) (PE.sym (wk1Subst-wk1 A)) here)

  -- Well-formed contexts from well-formed heaps

  wfHeap : Δ ⊢ʰ H ∷ Γ → ⊢ Δ
  wfHeap {Δ = ε} ε = ε
  wfHeap (⊢H ∙ ⊢t) = wfHeap ⊢H
  wfHeap (⊢H ∙● ⊢A) =
    let ⊢Δ = wfHeap ⊢H
    in  ⊢Δ ∙ substitution ⊢A (⊢ʰ→⊢ˢ ⊢H) ⊢Δ

opaque

  -- A well-formed type applied to a well-formed heap (as a substitution)
  -- is well-formed

  substHeap : Δ ⊢ʰ H ∷ Γ → Γ ⊢ A → Δ ⊢ A [ H ]ₕ
  substHeap ⊢H ⊢A =
    substitution ⊢A (⊢ʰ→⊢ˢ ⊢H) (wfHeap ⊢H)

opaque

  -- A well-formed term applied to a well-formed heap (as a substitution)
  -- is well-formed

  substHeapTerm : Δ ⊢ʰ H ∷ Γ → Γ ⊢ t ∷ A → Δ ⊢ t [ H ]ₕ ∷ A [ H ]ₕ
  substHeapTerm ⊢H ⊢t =
    substitutionTerm ⊢t (⊢ʰ→⊢ˢ ⊢H) (wfHeap ⊢H)

opaque

  -- A well-formed type equality applied to a well-formed heap
  -- (as a substitution) is well-formed

  substHeapEq : Δ ⊢ʰ H ∷ Γ → Γ ⊢ A ≡ B → Δ ⊢ A [ H ]ₕ ≡ B [ H ]ₕ
  substHeapEq ⊢H ⊢A≡B =
    substitutionEq ⊢A≡B (substRefl (⊢ʰ→⊢ˢ ⊢H)) (wfHeap ⊢H)

opaque

  -- A well-formed term equality  applied to a well-formed heap
  -- (as a substitution) is well-formed

  substHeapEqTerm : Δ ⊢ʰ H ∷ Γ → Γ ⊢ t ≡ u ∷ A
                  → Δ ⊢ t [ H ]ₕ ≡ u [ H ]ₕ ∷ A [ H ]ₕ
  substHeapEqTerm ⊢H ⊢t≡u =
    substitutionEqTerm ⊢t≡u (substRefl (⊢ʰ→⊢ˢ ⊢H)) (wfHeap ⊢H)

opaque

  -- Applying a well-formed heap as a substitution to a reduction

  substHeapRedTerm : Δ ⊢ʰ H ∷ Γ → Γ ⊢ t ⇒ u ∷ A
                   → Δ ⊢ t [ H ]ₕ ⇒ u [ H ]ₕ ∷ A [ H ]ₕ
  substHeapRedTerm ⊢H d =
    substitutionRedTerm d (⊢ʰ→⊢ˢ ⊢H) (wfHeap ⊢H)
