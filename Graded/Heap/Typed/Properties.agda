------------------------------------------------------------------------
-- Properties of stack and eliminator typing
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.Restrictions

module Graded.Heap.Typed.Properties
  {a} {M : Set a} {𝕄 : Modality M}
  (UR : Usage-restrictions 𝕄)
  (TR : Type-restrictions 𝕄)
  where

open Type-restrictions TR

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M
open import Definition.Typed TR
open import Definition.Typed.Inversion TR
open import Definition.Typed.Properties TR
open import Definition.Typed.Substitution TR
open import Definition.Typed.Syntactic TR
open import Definition.Typed.Consequences.Admissible TR
open import Definition.Typed.Consequences.Inequality TR

open import Graded.Heap.Typed UR TR
open import Graded.Heap.Typed.Inversion UR TR
open import Graded.Heap.Untyped type-variant UR
open import Graded.Heap.Untyped.Properties type-variant UR

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (1+)
open import Tools.Product
open import Tools.Relation
import Tools.PropositionalEquality as PE

private variable
  H : Heap _ _
  Γ Δ : Con Term _
  t u A B : Term _
  l : Universe-level
  e : Elim _
  S : Stack _
  s : State _ _ _
  x : Fin _
  ρ : Wk _ _

opaque

  -- Typing of erased heaps

  ⊢erasedHeap : ∀ {n} {Δ : Con Term n} → ⊢ Δ → Δ ⊢ʰ erasedHeap n ∷ Δ
  ⊢erasedHeap {0} {(ε)} ⊢Δ = ε
  ⊢erasedHeap {n = 1+ n} {Δ = Δ ∙ A} (∙ ⊢A) =
    PE.subst (λ x → Δ ∙ x ⊢ʰ _ ∷ Δ ∙ A)
      (erasedHeap-subst A)
      (⊢erasedHeap (wf ⊢A) ∙● ⊢A)

opaque

 -- Typing of the initial state

  ⊢initial : Δ ⊢ t ∷ A → Δ ⊢ₛ initial t ∷ A
  ⊢initial {Δ} {t} {A} ⊢t =
    ⊢ₛ (⊢erasedHeap (wfTerm ⊢t))
      (PE.subst (Δ ⊢_∷ _) (lemma t) ⊢t) ε
    where
    lemma : ∀ {n} (t : Term n) → t PE.≡ wk id t [ erasedHeap _ ]ₕ
    lemma t = PE.sym (PE.trans (erasedHeap-subst (wk id t)) (wk-id t))

opaque

  -- Well-typed terms applied to well-typed eliminators are
  -- well-typed under a heap substitution.

  ⊢⦅⦆ᵉ : Δ ⨾ H ⊢ᵉ e ⟨ t ⟩∷ A ↝ B
      → Δ ⊢ t [ H ]ₕ ∷ A
      → Δ ⊢ ⦅ e ⦆ᵉ t [ H ]ₕ ∷ B
  ⊢⦅⦆ᵉ (∘ₑ ⊢u _) ⊢t =
    ⊢t ∘ⱼ ⊢u
  ⊢⦅⦆ᵉ (fstₑ _) ⊢t =
    fstⱼ′ ⊢t
  ⊢⦅⦆ᵉ (sndₑ _) ⊢t =
    sndⱼ′ ⊢t
  ⊢⦅⦆ᵉ (prodrecₑ ⊢u ⊢A) ⊢t =
    prodrecⱼ′ ⊢A ⊢t ⊢u
  ⊢⦅⦆ᵉ (natrecₑ ⊢z ⊢s) ⊢t =
    natrecⱼ ⊢z ⊢s ⊢t
  ⊢⦅⦆ᵉ (unitrecₑ ⊢u ⊢A no-η) ⊢t =
    unitrecⱼ′ ⊢A ⊢t ⊢u
  ⊢⦅⦆ᵉ (emptyrecₑ ⊢A) ⊢t =
    emptyrecⱼ ⊢A ⊢t
  ⊢⦅⦆ᵉ (Jₑ ⊢u ⊢B) ⊢t =
    Jⱼ′ ⊢B ⊢u ⊢t
  ⊢⦅⦆ᵉ (Kₑ ⊢u ⊢B ok) ⊢t =
    Kⱼ ⊢B ⊢u ⊢t ok
  ⊢⦅⦆ᵉ ([]-congₑ ok) ⊢t =
    []-congⱼ′ ok ⊢t
  ⊢⦅⦆ᵉ (conv ⊢e B≡B′) ⊢t =
    conv (⊢⦅⦆ᵉ ⊢e ⊢t) B≡B′

opaque

  -- Well-typed terms applied to well-typed stacks are
  -- well-typed under a heap substitution.

  ⊢⦅⦆ˢ : Δ ⨾ H ⊢ S ⟨ t ⟩∷ A ↝ B
      → Δ ⊢ t [ H ]ₕ ∷ A
      → Δ ⊢ ⦅ S ⦆ˢ t [ H ]ₕ ∷ B
  ⊢⦅⦆ˢ ε ⊢t = ⊢t
  ⊢⦅⦆ˢ {H} {S = e ∙ S} {t} (⊢e ∙ ⊢S) ⊢t =
    ⊢⦅⦆ˢ ⊢S (⊢⦅⦆ᵉ ⊢e ⊢t)

opaque

  -- Well-typed states are well-typed when translated into terms

  ⊢⦅⦆ : Δ ⊢ₛ s ∷ A → Δ ⊢ ⦅ s ⦆ ∷ A
  ⊢⦅⦆ (⊢ₛ _ ⊢t ⊢S) = ⊢⦅⦆ˢ ⊢S ⊢t

opaque

  -- Equal terms are equal when applied to eliminators under
  -- heap substitutions.

  ⊢⦅⦆ᵉ-cong : Δ ⨾ H ⊢ᵉ e ⟨ t ⟩∷ A ↝ B
           → Δ ⊢ t [ H ]ₕ ≡ u [ H ]ₕ ∷ A
           → Δ ⊢ ⦅ e ⦆ᵉ t [ H ]ₕ ≡ ⦅ e ⦆ᵉ u [ H ]ₕ ∷ B
  ⊢⦅⦆ᵉ-cong (∘ₑ ⊢u _) t≡u =
    app-cong t≡u (refl ⊢u)
  ⊢⦅⦆ᵉ-cong (fstₑ _) t≡u =
    fst-cong′ t≡u
  ⊢⦅⦆ᵉ-cong (sndₑ _) t≡u =
    snd-cong′ t≡u
  ⊢⦅⦆ᵉ-cong (prodrecₑ ⊢v ⊢A) t≡u =
    prodrec-cong′ (refl ⊢A) t≡u (refl ⊢v)
  ⊢⦅⦆ᵉ-cong (natrecₑ ⊢z ⊢s) t≡u =
    natrec-cong (refl (⊢∙→⊢ (wfTerm ⊢s))) (refl ⊢z) (refl ⊢s) t≡u
  ⊢⦅⦆ᵉ-cong (unitrecₑ ⊢v ⊢A no-η) t≡u =
    unitrec-cong′ (refl ⊢A) t≡u (refl ⊢v)
  ⊢⦅⦆ᵉ-cong (emptyrecₑ ⊢A) t≡u =
    emptyrec-cong (refl ⊢A) t≡u
  ⊢⦅⦆ᵉ-cong (Jₑ ⊢u ⊢B) t≡u =
    case inversion-Id (syntacticEqTerm t≡u .proj₁) of λ
      (⊢A , ⊢t , ⊢v) →
    J-cong′ (refl ⊢A) (refl ⊢t) (refl ⊢B) (refl ⊢u) (refl ⊢v) t≡u
  ⊢⦅⦆ᵉ-cong (Kₑ ⊢u ⊢B ok) t≡u =
    case inversion-Id (syntacticEqTerm t≡u .proj₁) of λ
      (⊢A , ⊢t , _) →
    K-cong (refl ⊢A) (refl ⊢t) (refl ⊢B) (refl ⊢u) t≡u ok
  ⊢⦅⦆ᵉ-cong ([]-congₑ ok) t≡u =
    case inversion-Id (syntacticEqTerm t≡u .proj₁) of λ
      (⊢A , ⊢t , ⊢u) →
    []-cong-cong (refl ⊢A) (refl ⊢t) (refl ⊢u) t≡u ok
  ⊢⦅⦆ᵉ-cong (conv ⊢e B≡B′) t≡u =
    conv (⊢⦅⦆ᵉ-cong ⊢e t≡u) B≡B′

opaque

  -- Equal terms are equal when applied to stacks under
  -- heap substitutions.

  ⊢⦅⦆ˢ-cong : Δ ⨾ H ⊢ S ⟨ t ⟩∷ A ↝ B
           → Δ ⊢ t [ H ]ₕ ≡ u [ H ]ₕ ∷ A
           → Δ ⊢ ⦅ S ⦆ˢ t [ H ]ₕ ≡ ⦅ S ⦆ˢ u [ H ]ₕ ∷ B
  ⊢⦅⦆ˢ-cong ε t≡u = t≡u
  ⊢⦅⦆ˢ-cong {H} {S = e ∙ S} (⊢e ∙ ⊢S) t≡u =
    ⊢⦅⦆ˢ-cong ⊢S (⊢⦅⦆ᵉ-cong ⊢e t≡u)

opaque

  -- Applying terms to eliminators respects reduction

  ⊢⦅⦆ᵉ-subst : Δ ⨾ H ⊢ᵉ e ⟨ t ⟩∷ A ↝ B
            → Δ ⊢ t [ H ]ₕ ⇒ u [ H ]ₕ ∷ A
            → Δ ⊢ ⦅ e ⦆ᵉ t [ H ]ₕ ⇒ ⦅ e ⦆ᵉ u [ H ]ₕ ∷ B
  ⊢⦅⦆ᵉ-subst (∘ₑ ⊢u _) d =
    app-subst d ⊢u
  ⊢⦅⦆ᵉ-subst (fstₑ _) d =
    fst-subst′ d
  ⊢⦅⦆ᵉ-subst (sndₑ _) d =
    snd-subst′ d
  ⊢⦅⦆ᵉ-subst (prodrecₑ ⊢u ⊢A) d =
    prodrec-subst′ ⊢A ⊢u d
  ⊢⦅⦆ᵉ-subst (natrecₑ ⊢z ⊢s) d =
    natrec-subst ⊢z ⊢s d
  ⊢⦅⦆ᵉ-subst (unitrecₑ ⊢u ⊢A no-η) d =
    unitrec-subst′ ⊢A ⊢u d no-η
  ⊢⦅⦆ᵉ-subst (emptyrecₑ ⊢A) d =
    emptyrec-subst ⊢A d
  ⊢⦅⦆ᵉ-subst (Jₑ ⊢u ⊢B) d =
    J-subst′ ⊢B ⊢u d
  ⊢⦅⦆ᵉ-subst (Kₑ ⊢u ⊢B ok) d =
    K-subst ⊢B ⊢u d ok
  ⊢⦅⦆ᵉ-subst ([]-congₑ ok) d =
    []-cong-subst′ d ok
  ⊢⦅⦆ᵉ-subst (conv ⊢e B≡B′) d =
    conv (⊢⦅⦆ᵉ-subst ⊢e d) B≡B′

opaque

  -- Applying terms to stacks respects reduction

  ⊢⦅⦆ˢ-subst : Δ ⨾ H ⊢ S ⟨ t ⟩∷ A ↝ B
            → Δ ⊢ (t [ H ]ₕ) ⇒ (u [ H ]ₕ) ∷ A
            → Δ ⊢ ⦅ S ⦆ˢ t [ H ]ₕ ⇒ ⦅ S ⦆ˢ u [ H ]ₕ ∷ B
  ⊢⦅⦆ˢ-subst ε d = d
  ⊢⦅⦆ˢ-subst (⊢e ∙ ⊢S) d =
    ⊢⦅⦆ˢ-subst ⊢S (⊢⦅⦆ᵉ-subst ⊢e d)

opaque

  -- Conversion of the head term in eliminator typing

  ⊢ᵉ-convₜ : Δ ⨾ H ⊢ᵉ e ⟨ t ⟩∷ A ↝ B
           → Δ ⊢ t [ H ]ₕ ≡ u [ H ]ₕ ∷ A
           → Δ ⨾ H ⊢ᵉ e ⟨ u ⟩∷ A ↝ B
  ⊢ᵉ-convₜ (∘ₑ {A} {B} ⊢v ⊢B) t≡u =
    ∘ₑ {A = A} {B} ⊢v ⊢B
  ⊢ᵉ-convₜ (fstₑ ⊢B) t≡u =
    fstₑ ⊢B
  ⊢ᵉ-convₜ (sndₑ ⊢B) t≡u =
    conv (sndₑ ⊢B)
      (substTypeEq (refl ⊢B) (fst-cong′ (sym′ t≡u)))
  ⊢ᵉ-convₜ (prodrecₑ {B} {C} ⊢v ⊢A) t≡u =
    conv (prodrecₑ {B = B} {C} ⊢v ⊢A)
      (substTypeEq (refl ⊢A) (sym′ t≡u))
  ⊢ᵉ-convₜ (natrecₑ ⊢z ⊢s) t≡u =
    conv (natrecₑ ⊢z ⊢s)
      (substTypeEq (refl (⊢∙→⊢ (wfTerm ⊢s))) (sym′ t≡u))
  ⊢ᵉ-convₜ (unitrecₑ ⊢v ⊢A no-η) t≡u =
    conv (unitrecₑ ⊢v ⊢A no-η)
      (substTypeEq (refl ⊢A) (sym′ t≡u))
  ⊢ᵉ-convₜ (emptyrecₑ ⊢A) t≡u =
    emptyrecₑ ⊢A
  ⊢ᵉ-convₜ {Δ} {H} {t} {u} (Jₑ ⊢u ⊢B) t≡u =
    case inversion-Id (syntacticEqTerm t≡u .proj₁) of λ
      (⊢A , ⊢t , ⊢v) →
    case PE.subst (_ ⊢ _ ∷_) (PE.sym (subst-id _)) ⊢v of λ
      ⊢v′ →
    case PE.subst (Δ ⊢ t [ H ]ₕ ≡ u [ H ]ₕ ∷_)
           (PE.sym (PE.cong₂ (λ A t → Id A t _)
             (wk1-sgSubst _ _) (wk1-sgSubst _ _))) t≡u of λ
      t≡u′ →
    conv (Jₑ ⊢u ⊢B)
      (substTypeEq₂ (refl ⊢B) (refl ⊢v) (sym′ t≡u′))
  ⊢ᵉ-convₜ {H} {t} {u} (Kₑ ⊢u ⊢B ok) t≡u =
    conv (Kₑ ⊢u ⊢B ok)
      (substTypeEq (refl ⊢B) (sym′ t≡u))
  ⊢ᵉ-convₜ {H} {t} {u} ([]-congₑ ok) t≡u =
    []-congₑ ok
  ⊢ᵉ-convₜ (conv ⊢e B≡B′) t≡u =
    conv (⊢ᵉ-convₜ ⊢e t≡u) B≡B′

opaque

  -- Conversion of the head term in stack typing

  ⊢ˢ-convₜ : Δ ⨾ H ⊢ S ⟨ t ⟩∷ A ↝ B
          → Δ ⊢ t [ H ]ₕ ≡ u [ H ]ₕ ∷ A
          → Δ ⨾ H ⊢ S ⟨ u ⟩∷ A ↝ B
  ⊢ˢ-convₜ ε t≡u = ε
  ⊢ˢ-convₜ (⊢e ∙ ⊢S) t≡u =
    ⊢ᵉ-convₜ ⊢e t≡u ∙ ⊢ˢ-convₜ ⊢S (⊢⦅⦆ᵉ-cong ⊢e t≡u)

opaque

  -- If a term applied to an eliminator is in whnf then the term was
  -- neutral and the applied eliminator is also neutral.

  ⊢whnf⦅⦆ᵉ : Δ ⨾ H ⊢ᵉ e ⟨ u ⟩∷ A ↝ B
          → Whnf (⦅ e ⦆ᵉ t)
          → Neutral t × Neutral (⦅ e ⦆ᵉ t)
  ⊢whnf⦅⦆ᵉ (∘ₑ x x₁) (ne (∘ₙ n)) = n , ∘ₙ n
  ⊢whnf⦅⦆ᵉ (fstₑ _) (ne (fstₙ n)) = n , fstₙ n
  ⊢whnf⦅⦆ᵉ (sndₑ _) (ne (sndₙ n)) = n , sndₙ n
  ⊢whnf⦅⦆ᵉ (prodrecₑ x x₁) (ne (prodrecₙ n)) = n , prodrecₙ n
  ⊢whnf⦅⦆ᵉ (natrecₑ _ _) (ne (natrecₙ n)) = n , natrecₙ n
  ⊢whnf⦅⦆ᵉ (unitrecₑ x x₁ x₂) (ne (unitrecₙ no-η n)) = n , unitrecₙ no-η n
  ⊢whnf⦅⦆ᵉ (emptyrecₑ x) (ne (emptyrecₙ n)) = n , emptyrecₙ n
  ⊢whnf⦅⦆ᵉ (Jₑ x x₁) (ne (Jₙ n)) = n , Jₙ n
  ⊢whnf⦅⦆ᵉ (Kₑ x x₁ x₂) (ne (Kₙ n)) = n , Kₙ n
  ⊢whnf⦅⦆ᵉ ([]-congₑ x) (ne ([]-congₙ n)) = n , []-congₙ n
  ⊢whnf⦅⦆ᵉ (conv ⊢e x) w = ⊢whnf⦅⦆ᵉ ⊢e w

opaque

  -- If a term applied to a stack is in whnf then the term was in whnf.

  ⊢whnf⦅⦆ˢ : Δ ⨾ H ⊢ S ⟨ u ⟩∷ A ↝ B
          → Whnf (⦅ S ⦆ˢ t)
          → Whnf t
  ⊢whnf⦅⦆ˢ ε w = w
  ⊢whnf⦅⦆ˢ (⊢e ∙ ⊢S) w =
    ne (⊢whnf⦅⦆ᵉ ⊢e (⊢whnf⦅⦆ˢ ⊢S w) .proj₁)


opaque

  -- If a term applied to a non-empty stack is in whnf then the term
  -- was neutral and the applied stack is also neutral.

  ⊢whnf⦅⦆ˢ′ : Δ ⨾ H ⊢ e ∙ S ⟨ u ⟩∷ A ↝ B
           → Whnf (⦅ e ∙ S ⦆ˢ t)
           → Neutral t
  ⊢whnf⦅⦆ˢ′ (⊢e ∙ ⊢S) w =
    ⊢whnf⦅⦆ᵉ ⊢e (⊢whnf⦅⦆ˢ ⊢S w) .proj₁

opaque

  -- Applying a term that is neutral at a variable to an eliminator
  -- gives a term that is neutral at the same variable.

  ⊢⦅⦆ᵉ-NeutralAt : Δ ⨾ H ⊢ᵉ e ⟨ t ⟩∷ A ↝ B
                → NeutralAt x t
                → NeutralAt x (⦅ e ⦆ᵉ t)
  ⊢⦅⦆ᵉ-NeutralAt (∘ₑ _ _) n = ∘ₙ n
  ⊢⦅⦆ᵉ-NeutralAt (fstₑ _) n = fstₙ n
  ⊢⦅⦆ᵉ-NeutralAt (sndₑ _) n = sndₙ n
  ⊢⦅⦆ᵉ-NeutralAt (prodrecₑ _ _) n = prodrecₙ n
  ⊢⦅⦆ᵉ-NeutralAt (natrecₑ _ _) n = natrecₙ n
  ⊢⦅⦆ᵉ-NeutralAt (unitrecₑ _ _ x) n = unitrecₙ x n
  ⊢⦅⦆ᵉ-NeutralAt (emptyrecₑ _) n = emptyrecₙ n
  ⊢⦅⦆ᵉ-NeutralAt (Jₑ _ _) n = Jₙ n
  ⊢⦅⦆ᵉ-NeutralAt (Kₑ _ _ _) n = Kₙ n
  ⊢⦅⦆ᵉ-NeutralAt ([]-congₑ _) n = []-congₙ n
  ⊢⦅⦆ᵉ-NeutralAt (conv ⊢e x) n = ⊢⦅⦆ᵉ-NeutralAt ⊢e n

opaque

  -- Applying a term that is neutral at a variable to a non-empty stack
  -- gives a term that is neutral at the same variable.

  ⊢⦅⦆ˢ-NeutralAt : Δ ⨾ H ⊢ S ⟨ t ⟩∷ A ↝ B
                → NeutralAt x t
                → NeutralAt x (⦅ S ⦆ˢ t)
  ⊢⦅⦆ˢ-NeutralAt ε n = n
  ⊢⦅⦆ˢ-NeutralAt (⊢e ∙ ⊢S) n =
    ⊢⦅⦆ˢ-NeutralAt ⊢S (⊢⦅⦆ᵉ-NeutralAt ⊢e n)

opaque

  -- In a constistent context, there is no well-typed stack and head of
  -- matching type containing emptyrec 𝟘

  ⊢ˢemptyrec₀∉S : Consistent Δ → Δ ⨾ H ⊢ S ⟨ t ⟩∷ A ↝ B → Δ ⊢ t [ H ]ₕ ∷ A → emptyrec₀∈ S → ⊥
  ⊢ˢemptyrec₀∉S _          ε        _  ()
  ⊢ˢemptyrec₀∉S consistent (⊢e ∙ _) ⊢t here =
    case inversion-emptyrecₑ ⊢e of λ {
      (_ , PE.refl , _) →
    consistent _ ⊢t}
  ⊢ˢemptyrec₀∉S consistent (⊢e ∙ ⊢S) ⊢t (there d) =
    ⊢ˢemptyrec₀∉S consistent ⊢S (⊢⦅⦆ᵉ ⊢e ⊢t) d

opaque

  -- A version of the property above for well-typed states

  ⊢emptyrec₀∉S : Consistent Δ → Δ ⊢ₛ ⟨ H , t , ρ , S ⟩ ∷ A → emptyrec₀∈ S → ⊥
  ⊢emptyrec₀∉S consistent (⊢ₛ _ ⊢t ⊢S) x = ⊢ˢemptyrec₀∉S consistent ⊢S ⊢t x

opaque

  -- An eliminator's "hole type" is not definitionally equal to U l
  -- (given a certain assumption).

  hole-type-not-U :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    Δ ⨾ H ⊢ᵉ e ⟨ t ⟩∷ A ↝ B → ¬ Γ ⊢ A ≡ U l
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
  hole-type-not-U (conv ⊢e _)      = hole-type-not-U ⊢e
