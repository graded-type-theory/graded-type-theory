------------------------------------------------------------------------
-- Properties of stack and continuation typing
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.Restrictions
open import Graded.Usage.Restrictions.Natrec

module Graded.Heap.Typed.Properties
  {a} {M : Set a} {𝕄 : Modality M}
  (UR : Usage-restrictions 𝕄)
  (TR : Type-restrictions 𝕄)
  (open Usage-restrictions UR)
  (factoring-nr :
    ⦃ has-nr : Nr-available ⦄ →
    Is-factoring-nr M (Natrec-mode-Has-nr 𝕄 has-nr))
  where

open Type-restrictions TR
open Modality 𝕄

open import Definition.Untyped M
open import Definition.Untyped.Names-below M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M
open import Definition.Untyped.Whnf M type-variant
open import Definition.Typed TR
open import Definition.Typed.Inversion TR
open import Definition.Typed.Names-below TR
open import Definition.Typed.Properties TR
open import Definition.Typed.Substitution TR
open import Definition.Typed.Syntactic TR
open import Definition.Typed.Consequences.Inequality TR

open import Graded.Heap.Typed UR TR factoring-nr
open import Graded.Heap.Typed.Inversion UR TR factoring-nr
open import Graded.Heap.Untyped type-variant UR factoring-nr
open import Graded.Heap.Untyped.Properties type-variant UR factoring-nr

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+)
open import Tools.Product
open import Tools.Relation
import Tools.PropositionalEquality as PE
open import Tools.Sum

private variable
  H : Heap _ _
  ∇ : DCon (Term 0) _
  Γ Δ : Con Term _
  t u A B : Term _
  l : Universe-level
  c : Cont _
  S : Stack _
  s : State _ _ _
  n : Nat
  x : Fin _
  y : Nat ⊎ Fin _
  ρ : Wk _ _
  σ : Subst _ _
  V : Set a

opaque

  -- Typing of erased heaps

  ⊢erasedHeap : ∀ {n} {Δ : Con Term n} → ε »⊢ Δ → Δ ⊢ʰ erasedHeap n ∷ Δ
  ⊢erasedHeap {0} {(ε)} ⊢Δ = ε
  ⊢erasedHeap {n = 1+ n} {Δ = Δ ∙ A} (∙ ⊢A) =
    PE.subst (λ x → Δ ∙ x ⊢ʰ _ ∷ Δ ∙ A)
      (erasedHeap-subst A)
      (⊢erasedHeap (wf ⊢A) ∙● ⊢A)

opaque

 -- Typing of the initial state

  ⊢initial : ε » Δ ⊢ t ∷ A → Δ ⊢ₛ initial t ∷ A
  ⊢initial {Δ} {t} {A} ⊢t =
    ⊢ₛ (⊢erasedHeap (wfTerm ⊢t))
      (PE.subst (_ ⊢_∷ _) (lemma t) ⊢t) ε
    where
    lemma : ∀ {n} (t : Term n) → t PE.≡ wk id t [ erasedHeap _ ]ₕ
    lemma t = PE.sym (PE.trans (erasedHeap-subst (wk id t)) (wk-id t))

opaque

  -- Well-typed terms applied to well-typed continuations are
  -- well-typed under a heap substitution.

  ⊢⦅⦆ᶜ : Δ ⨾ H ⊢ᶜ c ⟨ t ⟩∷ A ↝ B
      → ε » Δ ⊢ t [ H ]ₕ ∷ A
      → ε » Δ ⊢ ⦅ c ⦆ᶜ t [ H ]ₕ ∷ B
  ⊢⦅⦆ᶜ (∘ₑ ⊢u _) ⊢t =
    ⊢t ∘ⱼ ⊢u
  ⊢⦅⦆ᶜ (fstₑ _) ⊢t =
    fstⱼ′ ⊢t
  ⊢⦅⦆ᶜ (sndₑ _) ⊢t =
    sndⱼ′ ⊢t
  ⊢⦅⦆ᶜ (prodrecₑ ⊢u ⊢A) ⊢t =
    prodrecⱼ′ ⊢A ⊢t ⊢u
  ⊢⦅⦆ᶜ (natrecₑ ⊢z ⊢s) ⊢t =
    natrecⱼ ⊢z ⊢s ⊢t
  ⊢⦅⦆ᶜ (unitrecₑ ⊢u ⊢A no-η) ⊢t =
    unitrecⱼ′ ⊢A ⊢t ⊢u
  ⊢⦅⦆ᶜ (emptyrecₑ ⊢A) ⊢t =
    emptyrecⱼ ⊢A ⊢t
  ⊢⦅⦆ᶜ (Jₑ ⊢u ⊢B) ⊢t =
    Jⱼ′ ⊢B ⊢u ⊢t
  ⊢⦅⦆ᶜ (Kₑ ⊢u ⊢B ok) ⊢t =
    Kⱼ ⊢B ⊢u ⊢t ok
  ⊢⦅⦆ᶜ ([]-congₑ ok) ⊢t =
    []-congⱼ′ ok ⊢t
  ⊢⦅⦆ᶜ (conv ⊢c B≡B′) ⊢t =
    conv (⊢⦅⦆ᶜ ⊢c ⊢t) B≡B′

opaque

  -- Well-typed terms applied to well-typed stacks are
  -- well-typed under a heap substitution.

  ⊢⦅⦆ˢ : Δ ⨾ H ⊢ S ⟨ t ⟩∷ A ↝ B
      → ε » Δ ⊢ t [ H ]ₕ ∷ A
      → ε » Δ ⊢ ⦅ S ⦆ˢ t [ H ]ₕ ∷ B
  ⊢⦅⦆ˢ ε ⊢t = ⊢t
  ⊢⦅⦆ˢ {H} {S = c ∙ S} {t} (⊢c ∙ ⊢S) ⊢t =
    ⊢⦅⦆ˢ ⊢S (⊢⦅⦆ᶜ ⊢c ⊢t)

opaque

  -- Well-typed states are well-typed when translated into terms

  ⊢⦅⦆ : Δ ⊢ₛ s ∷ A → ε » Δ ⊢ ⦅ s ⦆ ∷ A
  ⊢⦅⦆ (⊢ₛ _ ⊢t ⊢S) = ⊢⦅⦆ˢ ⊢S ⊢t

opaque

  -- Equal terms are equal when applied to continuations under
  -- heap substitutions.

  ⊢⦅⦆ᶜ-cong : Δ ⨾ H ⊢ᶜ c ⟨ t ⟩∷ A ↝ B
           → ε » Δ ⊢ t [ H ]ₕ ≡ u [ H ]ₕ ∷ A
           → ε » Δ ⊢ ⦅ c ⦆ᶜ t [ H ]ₕ ≡ ⦅ c ⦆ᶜ u [ H ]ₕ ∷ B
  ⊢⦅⦆ᶜ-cong (∘ₑ ⊢u _) t≡u =
    app-cong t≡u (refl ⊢u)
  ⊢⦅⦆ᶜ-cong (fstₑ _) t≡u =
    fst-cong′ t≡u
  ⊢⦅⦆ᶜ-cong (sndₑ _) t≡u =
    snd-cong′ t≡u
  ⊢⦅⦆ᶜ-cong (prodrecₑ ⊢v ⊢A) t≡u =
    prodrec-cong′ (refl ⊢A) t≡u (refl ⊢v)
  ⊢⦅⦆ᶜ-cong (natrecₑ ⊢z ⊢s) t≡u =
    natrec-cong (refl (⊢∙→⊢ (wfTerm ⊢s))) (refl ⊢z) (refl ⊢s) t≡u
  ⊢⦅⦆ᶜ-cong (unitrecₑ ⊢v ⊢A no-η) t≡u =
    unitrec-cong′ (refl ⊢A) t≡u (refl ⊢v)
  ⊢⦅⦆ᶜ-cong (emptyrecₑ ⊢A) t≡u =
    emptyrec-cong (refl ⊢A) t≡u
  ⊢⦅⦆ᶜ-cong (Jₑ ⊢u ⊢B) t≡u =
    case inversion-Id (syntacticEqTerm t≡u .proj₁) of λ
      (⊢A , ⊢t , ⊢v) →
    J-cong′ (refl ⊢A) (refl ⊢t) (refl ⊢B) (refl ⊢u) (refl ⊢v) t≡u
  ⊢⦅⦆ᶜ-cong (Kₑ ⊢u ⊢B ok) t≡u =
    case inversion-Id (syntacticEqTerm t≡u .proj₁) of λ
      (⊢A , ⊢t , _) →
    K-cong (refl ⊢A) (refl ⊢t) (refl ⊢B) (refl ⊢u) t≡u ok
  ⊢⦅⦆ᶜ-cong ([]-congₑ ok) t≡u =
    case inversion-Id (syntacticEqTerm t≡u .proj₁) of λ
      (⊢A , ⊢t , ⊢u) →
    []-cong-cong (refl ⊢A) (refl ⊢t) (refl ⊢u) t≡u ok
  ⊢⦅⦆ᶜ-cong (conv ⊢c B≡B′) t≡u =
    conv (⊢⦅⦆ᶜ-cong ⊢c t≡u) B≡B′

opaque

  -- Equal terms are equal when applied to stacks under
  -- heap substitutions.

  ⊢⦅⦆ˢ-cong : Δ ⨾ H ⊢ S ⟨ t ⟩∷ A ↝ B
           → ε » Δ ⊢ t [ H ]ₕ ≡ u [ H ]ₕ ∷ A
           → ε » Δ ⊢ ⦅ S ⦆ˢ t [ H ]ₕ ≡ ⦅ S ⦆ˢ u [ H ]ₕ ∷ B
  ⊢⦅⦆ˢ-cong ε t≡u = t≡u
  ⊢⦅⦆ˢ-cong {H} {S = c ∙ S} (⊢c ∙ ⊢S) t≡u =
    ⊢⦅⦆ˢ-cong ⊢S (⊢⦅⦆ᶜ-cong ⊢c t≡u)

opaque

  -- Applying terms to continuations respects reduction

  ⊢⦅⦆ᶜ-subst : Δ ⨾ H ⊢ᶜ c ⟨ t ⟩∷ A ↝ B
            → ε » Δ ⊢ t [ H ]ₕ ⇒ u [ H ]ₕ ∷ A
            → ε » Δ ⊢ ⦅ c ⦆ᶜ t [ H ]ₕ ⇒ ⦅ c ⦆ᶜ u [ H ]ₕ ∷ B
  ⊢⦅⦆ᶜ-subst (∘ₑ ⊢u _) d =
    app-subst d ⊢u
  ⊢⦅⦆ᶜ-subst (fstₑ _) d =
    fst-subst′ d
  ⊢⦅⦆ᶜ-subst (sndₑ _) d =
    snd-subst′ d
  ⊢⦅⦆ᶜ-subst (prodrecₑ ⊢u ⊢A) d =
    prodrec-subst′ ⊢A ⊢u d
  ⊢⦅⦆ᶜ-subst (natrecₑ ⊢z ⊢s) d =
    natrec-subst ⊢z ⊢s d
  ⊢⦅⦆ᶜ-subst (unitrecₑ ⊢u ⊢A no-η) d =
    unitrec-subst′ ⊢A ⊢u d no-η
  ⊢⦅⦆ᶜ-subst (emptyrecₑ ⊢A) d =
    emptyrec-subst ⊢A d
  ⊢⦅⦆ᶜ-subst (Jₑ ⊢u ⊢B) d =
    J-subst′ ⊢B ⊢u d
  ⊢⦅⦆ᶜ-subst (Kₑ ⊢u ⊢B ok) d =
    K-subst ⊢B ⊢u d ok
  ⊢⦅⦆ᶜ-subst ([]-congₑ ok) d =
    []-cong-subst′ d ok
  ⊢⦅⦆ᶜ-subst (conv ⊢c B≡B′) d =
    conv (⊢⦅⦆ᶜ-subst ⊢c d) B≡B′

opaque

  -- Applying terms to stacks respects reduction

  ⊢⦅⦆ˢ-subst : Δ ⨾ H ⊢ S ⟨ t ⟩∷ A ↝ B
            → ε » Δ ⊢ (t [ H ]ₕ) ⇒ (u [ H ]ₕ) ∷ A
            → ε » Δ ⊢ ⦅ S ⦆ˢ t [ H ]ₕ ⇒ ⦅ S ⦆ˢ u [ H ]ₕ ∷ B
  ⊢⦅⦆ˢ-subst ε d = d
  ⊢⦅⦆ˢ-subst (⊢c ∙ ⊢S) d =
    ⊢⦅⦆ˢ-subst ⊢S (⊢⦅⦆ᶜ-subst ⊢c d)

opaque

  -- Conversion of the head term in continuations typing

  ⊢ᶜ-convₜ : Δ ⨾ H ⊢ᶜ c ⟨ t ⟩∷ A ↝ B
           → ε » Δ ⊢ t [ H ]ₕ ≡ u [ H ]ₕ ∷ A
           → Δ ⨾ H ⊢ᶜ c ⟨ u ⟩∷ A ↝ B
  ⊢ᶜ-convₜ (∘ₑ {A} {B} ⊢v ⊢B) t≡u =
    ∘ₑ {A = A} {B} ⊢v ⊢B
  ⊢ᶜ-convₜ (fstₑ ⊢B) t≡u =
    fstₑ ⊢B
  ⊢ᶜ-convₜ (sndₑ ⊢B) t≡u =
    conv (sndₑ ⊢B)
      (substTypeEq (refl ⊢B) (fst-cong′ (sym′ t≡u)))
  ⊢ᶜ-convₜ (prodrecₑ {B} {C} ⊢v ⊢A) t≡u =
    conv (prodrecₑ {B = B} {C} ⊢v ⊢A)
      (substTypeEq (refl ⊢A) (sym′ t≡u))
  ⊢ᶜ-convₜ (natrecₑ ⊢z ⊢s) t≡u =
    conv (natrecₑ ⊢z ⊢s)
      (substTypeEq (refl (⊢∙→⊢ (wfTerm ⊢s))) (sym′ t≡u))
  ⊢ᶜ-convₜ (unitrecₑ ⊢v ⊢A no-η) t≡u =
    conv (unitrecₑ ⊢v ⊢A no-η)
      (substTypeEq (refl ⊢A) (sym′ t≡u))
  ⊢ᶜ-convₜ (emptyrecₑ ⊢A) t≡u =
    emptyrecₑ ⊢A
  ⊢ᶜ-convₜ {Δ} {H} {t} {u} (Jₑ ⊢u ⊢B) t≡u =
    case inversion-Id (syntacticEqTerm t≡u .proj₁) of λ
      (⊢A , ⊢t , ⊢v) →
    case PE.subst (_ ⊢ _ ∷_) (PE.sym (subst-id _)) ⊢v of λ
      ⊢v′ →
    case PE.subst (_⊢_≡_∷_ _ _ _)
           (PE.sym (PE.cong₂ (λ A t → Id A t _)
             (wk1-sgSubst _ _) (wk1-sgSubst _ _))) t≡u of λ
      t≡u′ →
    conv (Jₑ ⊢u ⊢B)
      (substTypeEq₂ (refl ⊢B) (refl ⊢v) (sym′ t≡u′))
  ⊢ᶜ-convₜ {H} {t} {u} (Kₑ ⊢u ⊢B ok) t≡u =
    conv (Kₑ ⊢u ⊢B ok)
      (substTypeEq (refl ⊢B) (sym′ t≡u))
  ⊢ᶜ-convₜ {H} {t} {u} ([]-congₑ ok) t≡u =
    []-congₑ ok
  ⊢ᶜ-convₜ (conv ⊢c B≡B′) t≡u =
    conv (⊢ᶜ-convₜ ⊢c t≡u) B≡B′

opaque

  -- Conversion of the head term in stack typing

  ⊢ˢ-convₜ : Δ ⨾ H ⊢ S ⟨ t ⟩∷ A ↝ B
          → ε » Δ ⊢ t [ H ]ₕ ≡ u [ H ]ₕ ∷ A
          → Δ ⨾ H ⊢ S ⟨ u ⟩∷ A ↝ B
  ⊢ˢ-convₜ ε t≡u = ε
  ⊢ˢ-convₜ (⊢c ∙ ⊢S) t≡u =
    ⊢ᶜ-convₜ ⊢c t≡u ∙ ⊢ˢ-convₜ ⊢S (⊢⦅⦆ᶜ-cong ⊢c t≡u)

opaque

  -- If a term applied to a continuation is in whnf then the term was
  -- neutral and the applied continuation is also neutral.

  ⊢whnf⦅⦆ᶜ : Δ ⨾ H ⊢ᶜ c ⟨ u ⟩∷ A ↝ B
          → Whnf ∇ (⦅ c ⦆ᶜ t)
          → Neutral⁺ ∇ t × Neutral⁺ ∇ (⦅ c ⦆ᶜ t)
  ⊢whnf⦅⦆ᶜ (∘ₑ x x₁) (ne (∘ₙ n)) = n , ∘ₙ n
  ⊢whnf⦅⦆ᶜ (fstₑ _) (ne (fstₙ n)) = n , fstₙ n
  ⊢whnf⦅⦆ᶜ (sndₑ _) (ne (sndₙ n)) = n , sndₙ n
  ⊢whnf⦅⦆ᶜ (prodrecₑ x x₁) (ne (prodrecₙ n)) = n , prodrecₙ n
  ⊢whnf⦅⦆ᶜ (natrecₑ _ _) (ne (natrecₙ n)) = n , natrecₙ n
  ⊢whnf⦅⦆ᶜ (unitrecₑ x x₁ x₂) (ne (unitrecₙ no-η n)) = n , unitrecₙ no-η n
  ⊢whnf⦅⦆ᶜ (emptyrecₑ x) (ne (emptyrecₙ n)) = n , emptyrecₙ n
  ⊢whnf⦅⦆ᶜ (Jₑ x x₁) (ne (Jₙ n)) = n , Jₙ n
  ⊢whnf⦅⦆ᶜ (Kₑ x x₁ x₂) (ne (Kₙ n)) = n , Kₙ n
  ⊢whnf⦅⦆ᶜ ([]-congₑ x) (ne ([]-congₙ n)) = n , []-congₙ n
  ⊢whnf⦅⦆ᶜ (conv ⊢c x) w = ⊢whnf⦅⦆ᶜ ⊢c w

opaque

  -- If a term applied to a stack is in whnf then the term was in whnf.

  ⊢whnf⦅⦆ˢ : Δ ⨾ H ⊢ S ⟨ u ⟩∷ A ↝ B
          → Whnf ∇ (⦅ S ⦆ˢ t)
          → Whnf ∇ t
  ⊢whnf⦅⦆ˢ ε w = w
  ⊢whnf⦅⦆ˢ (⊢c ∙ ⊢S) w =
    ne (⊢whnf⦅⦆ᶜ ⊢c (⊢whnf⦅⦆ˢ ⊢S w) .proj₁)


opaque

  -- If a term applied to a non-empty stack is in whnf then the term
  -- was neutral and the applied stack is also neutral.

  ⊢whnf⦅⦆ˢ′ : Δ ⨾ H ⊢ c ∙ S ⟨ u ⟩∷ A ↝ B
           → Whnf ∇ (⦅ c ∙ S ⦆ˢ t)
           → Neutral⁺ ∇ t
  ⊢whnf⦅⦆ˢ′ (⊢c ∙ ⊢S) w =
    ⊢whnf⦅⦆ᶜ ⊢c (⊢whnf⦅⦆ˢ ⊢S w) .proj₁

opaque

  -- Applying a term that is neutral at a variable to a continuation
  -- gives a term that is neutral at the same variable.

  ⊢⦅⦆ᶜ-NeutralAt : Δ ⨾ H ⊢ᶜ c ⟨ t ⟩∷ A ↝ B
                → NeutralAt V ∇ y t
                → NeutralAt V ∇ y (⦅ c ⦆ᶜ t)
  ⊢⦅⦆ᶜ-NeutralAt (∘ₑ _ _) n = ∘ₙ n
  ⊢⦅⦆ᶜ-NeutralAt (fstₑ _) n = fstₙ n
  ⊢⦅⦆ᶜ-NeutralAt (sndₑ _) n = sndₙ n
  ⊢⦅⦆ᶜ-NeutralAt (prodrecₑ _ _) n = prodrecₙ n
  ⊢⦅⦆ᶜ-NeutralAt (natrecₑ _ _) n = natrecₙ n
  ⊢⦅⦆ᶜ-NeutralAt (unitrecₑ _ _ x) n = unitrecₙ x n
  ⊢⦅⦆ᶜ-NeutralAt (emptyrecₑ _) n = emptyrecₙ n
  ⊢⦅⦆ᶜ-NeutralAt (Jₑ _ _) n = Jₙ n
  ⊢⦅⦆ᶜ-NeutralAt (Kₑ _ _ _) n = Kₙ n
  ⊢⦅⦆ᶜ-NeutralAt ([]-congₑ _) n = []-congₙ n
  ⊢⦅⦆ᶜ-NeutralAt (conv ⊢c x) n = ⊢⦅⦆ᶜ-NeutralAt ⊢c n

opaque

  -- Applying a term that is neutral at a variable to a non-empty stack
  -- gives a term that is neutral at the same variable.

  ⊢⦅⦆ˢ-NeutralAt : Δ ⨾ H ⊢ S ⟨ t ⟩∷ A ↝ B
                → NeutralAt V ∇ y t
                → NeutralAt V ∇ y (⦅ S ⦆ˢ t)
  ⊢⦅⦆ˢ-NeutralAt ε n = n
  ⊢⦅⦆ˢ-NeutralAt (⊢c ∙ ⊢S) n =
    ⊢⦅⦆ˢ-NeutralAt ⊢S (⊢⦅⦆ᶜ-NeutralAt ⊢c n)

opaque

  -- In a constistent context, there is no well-typed stack and head of
  -- matching type containing emptyrec 𝟘

  ⊢ˢemptyrec₀∉S :
    Consistent (ε » Δ) → Δ ⨾ H ⊢ S ⟨ t ⟩∷ A ↝ B → ε » Δ ⊢ t [ H ]ₕ ∷ A →
    emptyrec 𝟘 ∈ S → ⊥
  ⊢ˢemptyrec₀∉S _          ε        _  ()
  ⊢ˢemptyrec₀∉S consistent (⊢c ∙ _) ⊢t here =
    case inversion-emptyrecₑ ⊢c of λ {
      (_ , PE.refl , _) →
    consistent _ ⊢t}
  ⊢ˢemptyrec₀∉S consistent (⊢c ∙ ⊢S) ⊢t (there d) =
    ⊢ˢemptyrec₀∉S consistent ⊢S (⊢⦅⦆ᶜ ⊢c ⊢t) d

opaque

  -- A version of the property above for well-typed states

  ⊢emptyrec₀∉S :
    Consistent (ε » Δ) → Δ ⊢ₛ ⟨ H , t , ρ , S ⟩ ∷ A → emptyrec 𝟘 ∈ S → ⊥
  ⊢emptyrec₀∉S consistent (⊢ₛ _ ⊢t ⊢S) x = ⊢ˢemptyrec₀∉S consistent ⊢S ⊢t x

opaque

  -- A continuation's "hole type" is not definitionally equal to U l
  -- (given a certain assumption).

  hole-type-not-U :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    Δ ⨾ H ⊢ᶜ c ⟨ t ⟩∷ A ↝ B → ¬ ε » Γ ⊢ A ≡ U l
  hole-type-not-U (∘ₑ _ _)         = U≢ΠΣⱼ ∘→ sym
  hole-type-not-U (fstₑ _)         = U≢ΠΣⱼ ∘→ sym
  hole-type-not-U (sndₑ _)         = U≢ΠΣⱼ ∘→ sym
  hole-type-not-U (prodrecₑ _ _)   = U≢ΠΣⱼ ∘→ sym
  hole-type-not-U (natrecₑ _ _)    = U≢ℕ ∘→ sym
  hole-type-not-U (unitrecₑ _ _ _) = U≢Unitⱼ ∘→ sym
  hole-type-not-U (emptyrecₑ _)    = U≢Emptyⱼ ∘→ sym
  hole-type-not-U (Jₑ _ _)         = Id≢U
  hole-type-not-U (Kₑ _ _ _)       = Id≢U
  hole-type-not-U ([]-congₑ _)     = Id≢U
  hole-type-not-U (conv ⊢c _)      = hole-type-not-U ⊢c

private opaque

  -- A variant of ⊢∷→Names<.

  ⊢∷→Names<′ :
    {∇ : DCon (Term 0) n} →
    ∇ » Γ ⊢ wk ρ t [ σ ] ∷ A → Names< n t
  ⊢∷→Names<′ = Names<-wk→ ∘→ Names<-[]→ ∘→ ⊢∷→Names<

opaque

  -- Well-formed heaps do not contain names.

  ⊢ʰ→No-namesʰ : Δ ⊢ʰ H ∷ Γ → No-namesʰ H
  ⊢ʰ→No-namesʰ ε =
    ε
  ⊢ʰ→No-namesʰ (⊢H ∙ ⊢t) =
    ⊢ʰ→No-namesʰ ⊢H ∙ ⊢∷→Names<′ ⊢t
  ⊢ʰ→No-namesʰ (⊢H ∙● ⊢A) =
    ⊢ʰ→No-namesʰ ⊢H ∙●

opaque

  -- If Δ ⊢ₛ s ∷ A holds, then No-namesₛ′ s holds.

  ⊢ₛ→No-namesₛ′ : Δ ⊢ₛ s ∷ A → No-namesₛ′ s
  ⊢ₛ→No-namesₛ′ (⊢ₛ ⊢H ⊢t _) =
    ⊢ʰ→No-namesʰ ⊢H , ⊢∷→Names<′ ⊢t
