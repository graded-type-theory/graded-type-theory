------------------------------------------------------------------------
-- Properties of well-formed heaps as substitutions
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.Restrictions
open import Graded.Usage.Restrictions.Natrec

module Graded.Heap.Typed.Substitution
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
open import Definition.Untyped.Properties M
open import Definition.Typed TR
open import Definition.Typed.Properties TR
open import Definition.Typed.Substitution TR

open import Graded.Heap.Typed UR TR factoring-nr
open import Graded.Heap.Untyped type-variant UR factoring-nr

open import Tools.Function
open import Tools.Product
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

  ⊢ʰ→⊢ˢʷ : Δ ⊢ʰ H ∷ Γ → Δ ⊢ˢʷ toSubstₕ H ∷ Γ
  ⊢ʰ→⊢ˢʷ ε = ⊢ˢʷ∷ε⇔ .proj₂ ε
  ⊢ʰ→⊢ˢʷ (⊢H ∙ ⊢t) =
    →⊢ˢʷ∷∙ (⊢ʰ→⊢ˢʷ ⊢H) ⊢t
  ⊢ʰ→⊢ˢʷ (_∙●_ {Δ} {H} {A} ⊢H ⊢A) =
    let ⊢σ = ⊢ʰ→⊢ˢʷ ⊢H
        ⊢σA = subst-⊢ ⊢A ⊢σ
    in
    →⊢ˢʷ∷∙ (⊢ˢʷ∷-wk1Subst ⊢σA ⊢σ) $
    var (∙ ⊢σA)
      (PE.subst (y0 ∷_∈ Δ ∙ A [ H ]ₕ) (PE.sym (wk1Subst-wk1 A)) here)

  -- Well-formed contexts from well-formed heaps

  wfHeap : Δ ⊢ʰ H ∷ Γ → ⊢ Δ
  wfHeap {Δ = ε} ε = ε
  wfHeap (⊢H ∙ ⊢t) = wfHeap ⊢H
  wfHeap (⊢H ∙● ⊢A) =
    ∙ subst-⊢ ⊢A (⊢ʰ→⊢ˢʷ ⊢H)

opaque

  -- A well-formed type applied to a well-formed heap (as a substitution)
  -- is well-formed

  substHeap : Δ ⊢ʰ H ∷ Γ → Γ ⊢ A → Δ ⊢ A [ H ]ₕ
  substHeap ⊢H ⊢A =
    subst-⊢ ⊢A (⊢ʰ→⊢ˢʷ ⊢H)

opaque

  -- A well-formed term applied to a well-formed heap (as a substitution)
  -- is well-formed

  substHeapTerm : Δ ⊢ʰ H ∷ Γ → Γ ⊢ t ∷ A → Δ ⊢ t [ H ]ₕ ∷ A [ H ]ₕ
  substHeapTerm ⊢H ⊢t =
    subst-⊢∷ ⊢t (⊢ʰ→⊢ˢʷ ⊢H)

opaque

  -- A well-formed type equality applied to a well-formed heap
  -- (as a substitution) is well-formed

  substHeapEq : Δ ⊢ʰ H ∷ Γ → Γ ⊢ A ≡ B → Δ ⊢ A [ H ]ₕ ≡ B [ H ]ₕ
  substHeapEq ⊢H ⊢A≡B =
    subst-⊢≡ ⊢A≡B (refl-⊢ˢʷ≡∷ (⊢ʰ→⊢ˢʷ ⊢H))

opaque

  -- A well-formed term equality  applied to a well-formed heap
  -- (as a substitution) is well-formed

  substHeapEqTerm : Δ ⊢ʰ H ∷ Γ → Γ ⊢ t ≡ u ∷ A
                  → Δ ⊢ t [ H ]ₕ ≡ u [ H ]ₕ ∷ A [ H ]ₕ
  substHeapEqTerm ⊢H ⊢t≡u =
    subst-⊢≡∷ ⊢t≡u (refl-⊢ˢʷ≡∷ (⊢ʰ→⊢ˢʷ ⊢H))

opaque

  -- Applying a well-formed heap as a substitution to a reduction

  substHeapRedTerm : Δ ⊢ʰ H ∷ Γ → Γ ⊢ t ⇒ u ∷ A
                   → Δ ⊢ t [ H ]ₕ ⇒ u [ H ]ₕ ∷ A [ H ]ₕ
  substHeapRedTerm ⊢H d =
    subst-⊢⇒∷ d (⊢ʰ→⊢ˢʷ ⊢H)
