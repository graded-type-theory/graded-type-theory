------------------------------------------------------------------------
-- Properties of well-formed heaps as substitutions
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Mode
open import Graded.Usage.Restrictions
open import Definition.Typed.Restrictions
open import Graded.Usage.Restrictions.Natrec

module Graded.Heap.Typed.Substitution
  {a b} {M : Set a} {Mode : Set b}
  {𝕄 : Modality M}
  {𝐌 : IsMode Mode 𝕄}
  (UR : Usage-restrictions 𝕄 𝐌)
  (TR : Type-restrictions 𝕄)
  (open Usage-restrictions UR)
  (factoring-nr :
    ⦃ has-nr : Nr-available ⦄ →
    Is-factoring-nr M (Natrec-mode-Has-nr 𝕄 has-nr))
  (∣ε∣ : M)
  where

open Type-restrictions TR

open import Definition.Untyped M
open import Definition.Untyped.Properties M
open import Definition.Typed TR
open import Definition.Typed.Substitution TR

open import Graded.Heap.Typed UR TR factoring-nr ∣ε∣
open import Graded.Heap.Untyped type-variant UR factoring-nr ∣ε∣

open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE

private variable
  Γ Δ : Con Term _
  H H′ : Heap _ _
  ρ : Wk _ _
  t u A B : Term _
  y : Ptr _
  e : Entry _ _
  p : M
  c : Cont _
  S : Stack _
  σ : Subst _ _

opaque mutual

  -- A well-formed heap is a well-formed substitution

  ⊢ʰ→⊢ˢʷ : Δ ⊢ʰ H ∷ Γ → ε » Δ ⊢ˢʷ toSubstₕ H ∷ Γ
  ⊢ʰ→⊢ˢʷ ε = ⊢ˢʷ∷ε⇔ .proj₂ εε
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

  wfHeap : Δ ⊢ʰ H ∷ Γ → ε »⊢ Δ
  wfHeap {Δ = ε} ε = εε
  wfHeap (⊢H ∙ ⊢t) = wfHeap ⊢H
  wfHeap (⊢H ∙● ⊢A) =
    ∙ subst-⊢ ⊢A (⊢ʰ→⊢ˢʷ ⊢H)

opaque

  -- A well-formed type applied to a well-formed heap (as a substitution)
  -- is well-formed

  substHeap : Δ ⊢ʰ H ∷ Γ → ε » Γ ⊢ A → ε » Δ ⊢ A [ H ]ₕ
  substHeap ⊢H ⊢A =
    subst-⊢ ⊢A (⊢ʰ→⊢ˢʷ ⊢H)

opaque

  -- A well-formed term applied to a well-formed heap (as a substitution)
  -- is well-formed

  substHeapTerm :
    Δ ⊢ʰ H ∷ Γ → ε » Γ ⊢ t ∷ A → ε » Δ ⊢ t [ H ]ₕ ∷ A [ H ]ₕ
  substHeapTerm ⊢H ⊢t =
    subst-⊢∷ ⊢t (⊢ʰ→⊢ˢʷ ⊢H)

opaque

  -- A well-formed type equality applied to a well-formed heap
  -- (as a substitution) is well-formed

  substHeapEq : Δ ⊢ʰ H ∷ Γ → ε » Γ ⊢ A ≡ B → ε » Δ ⊢ A [ H ]ₕ ≡ B [ H ]ₕ
  substHeapEq ⊢H ⊢A≡B =
    subst-⊢≡ ⊢A≡B (refl-⊢ˢʷ≡∷ (⊢ʰ→⊢ˢʷ ⊢H))

opaque

  -- A well-formed term equality  applied to a well-formed heap
  -- (as a substitution) is well-formed

  substHeapEqTerm : Δ ⊢ʰ H ∷ Γ → ε » Γ ⊢ t ≡ u ∷ A
                  → ε » Δ ⊢ t [ H ]ₕ ≡ u [ H ]ₕ ∷ A [ H ]ₕ
  substHeapEqTerm ⊢H ⊢t≡u =
    subst-⊢≡∷ ⊢t≡u (refl-⊢ˢʷ≡∷ (⊢ʰ→⊢ˢʷ ⊢H))

opaque

  -- Applying a well-formed heap as a substitution to a reduction

  substHeapRedTerm : Δ ⊢ʰ H ∷ Γ → ε » Γ ⊢ t ⇒ u ∷ A
                   → ε » Δ ⊢ t [ H ]ₕ ⇒ u [ H ]ₕ ∷ A [ H ]ₕ
  substHeapRedTerm ⊢H d =
    subst-⊢⇒∷ d (⊢ʰ→⊢ˢʷ ⊢H)
