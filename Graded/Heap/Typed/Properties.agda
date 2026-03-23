------------------------------------------------------------------------
-- Properties of stack and continuation typing
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Mode
open import Graded.Usage.Restrictions
open import Definition.Typed.Restrictions
open import Graded.Usage.Restrictions.Natrec

module Graded.Heap.Typed.Properties
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
open Modality 𝕄

open import Definition.Untyped M
import Definition.Untyped.Erased 𝕄 as E
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
open import Definition.Typed.Well-formed TR
open import Definition.Typed.Consequences.Inequality TR

open import Graded.Heap.Typed UR TR factoring-nr ∣ε∣
open import Graded.Heap.Typed.Inversion UR TR factoring-nr ∣ε∣
open import Graded.Heap.Untyped type-variant UR factoring-nr ∣ε∣
open import Graded.Heap.Untyped.Properties type-variant UR factoring-nr ∣ε∣

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
  A B t u : Term _
  l : Lvl _
  c : Cont _
  S : Stack _
  s : State _ _ _
  n : Nat
  x : Fin _
  y : Nat ⊎ Fin _
  ρ ρ′ : Wk _ _
  σ σ′ : Subst _ _
  V : Set a
  p : M

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
    ⊢ₛ (⊢erasedHeap (wf ⊢t))
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
  ⊢⦅⦆ᶜ (lowerₑ _) ⊢t =
    lowerⱼ ⊢t
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
  ⊢⦅⦆ᶜ ([]-congₑ ok ⊢l) ⊢t =
    PE.subst (_⊢_∷_ _ _) (E.wk-Id-Erased-[]-[] _) $
    []-congⱼ′ ok ⊢l ⊢t
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
  ⊢⦅⦆ᶜ-cong (lowerₑ _) t≡u =
    lower-cong t≡u
  ⊢⦅⦆ᶜ-cong (∘ₑ ⊢u _) t≡u =
    app-cong t≡u (refl ⊢u)
  ⊢⦅⦆ᶜ-cong (fstₑ _) t≡u =
    fst-cong′ t≡u
  ⊢⦅⦆ᶜ-cong (sndₑ _) t≡u =
    snd-cong′ t≡u
  ⊢⦅⦆ᶜ-cong (prodrecₑ ⊢v ⊢A) t≡u =
    prodrec-cong′ (refl ⊢A) t≡u (refl ⊢v)
  ⊢⦅⦆ᶜ-cong (natrecₑ ⊢z ⊢s) t≡u =
    natrec-cong (refl (⊢∙→⊢ (wf ⊢s))) (refl ⊢z) (refl ⊢s) t≡u
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
  ⊢⦅⦆ᶜ-cong ([]-congₑ ok ⊢l) t≡u =
    let _ , ⊢t , ⊢u = inversion-Id (syntacticEqTerm t≡u .proj₁) in
    PE.subst (_⊢_≡_∷_ _ _ _) (E.wk-Id-Erased-[]-[] _) $
    []-cong-cong (refl-⊢≡∷L ⊢l) (refl (wf-⊢∷ ⊢t)) (refl ⊢t) (refl ⊢u)
      t≡u ok
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
  ⊢⦅⦆ᶜ-subst (lowerₑ _) d =
    lower-subst d
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
  ⊢⦅⦆ᶜ-subst ([]-congₑ ok ⊢l) d =
    PE.subst (_⊢_⇒_∷_ _ _ _) (E.wk-Id-Erased-[]-[] _) $
    []-cong-subst ⊢l d ok
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
  ⊢ᶜ-convₜ (lowerₑ ⊢B) t≡u =
    lowerₑ ⊢B
  ⊢ᶜ-convₜ (∘ₑ {A} {B} ⊢v ⊢B) t≡u =
    ∘ₑ {A = A} {B} ⊢v ⊢B
  ⊢ᶜ-convₜ (fstₑ ⊢B) t≡u =
    fstₑ ⊢B
  ⊢ᶜ-convₜ (sndₑ ⊢B) t≡u =
    conv (sndₑ ⊢B) (subst-⊢≡₀ ⊢B (fst-cong′ (sym′ t≡u)))
  ⊢ᶜ-convₜ (prodrecₑ {B} {C} ⊢v ⊢A) t≡u =
    conv (prodrecₑ {B = B} {C} ⊢v ⊢A)
      (subst-⊢≡₀ ⊢A (sym′ t≡u))
  ⊢ᶜ-convₜ (natrecₑ ⊢z ⊢s) t≡u =
    conv (natrecₑ ⊢z ⊢s) (subst-⊢≡₀ (⊢∙→⊢ (wf ⊢s)) (sym′ t≡u))
  ⊢ᶜ-convₜ (unitrecₑ ⊢v ⊢A no-η) t≡u =
    conv (unitrecₑ ⊢v ⊢A no-η) (subst-⊢≡₀ ⊢A (sym′ t≡u))
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
    conv (Jₑ ⊢u ⊢B) (subst-⊢≡₁₀ ⊢B (refl ⊢v) (sym′ t≡u′))
  ⊢ᶜ-convₜ {H} {t} {u} (Kₑ ⊢u ⊢B ok) t≡u =
    conv (Kₑ ⊢u ⊢B ok) (subst-⊢≡₀ ⊢B (sym′ t≡u))
  ⊢ᶜ-convₜ ([]-congₑ ok ⊢l) _ =
    []-congₑ ok ⊢l
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
  ⊢whnf⦅⦆ᶜ (lowerₑ _) (ne (lowerₙ n)) = n , lowerₙ n
  ⊢whnf⦅⦆ᶜ (∘ₑ x x₁) (ne (∘ₙ n)) = n , ∘ₙ n
  ⊢whnf⦅⦆ᶜ (fstₑ _) (ne (fstₙ n)) = n , fstₙ n
  ⊢whnf⦅⦆ᶜ (sndₑ _) (ne (sndₙ n)) = n , sndₙ n
  ⊢whnf⦅⦆ᶜ (prodrecₑ x x₁) (ne (prodrecₙ n)) = n , prodrecₙ n
  ⊢whnf⦅⦆ᶜ (natrecₑ _ _) (ne (natrecₙ n)) = n , natrecₙ n
  ⊢whnf⦅⦆ᶜ (unitrecₑ x x₁ x₂) (ne (unitrecₙ no-η n)) = n , unitrecₙ no-η n
  ⊢whnf⦅⦆ᶜ (emptyrecₑ x) (ne (emptyrecₙ n)) = n , emptyrecₙ n
  ⊢whnf⦅⦆ᶜ (Jₑ x x₁) (ne (Jₙ n)) = n , Jₙ n
  ⊢whnf⦅⦆ᶜ (Kₑ x x₁ x₂) (ne (Kₙ n)) = n , Kₙ n
  ⊢whnf⦅⦆ᶜ ([]-congₑ _ _) (ne ([]-congₙ n)) = n , []-congₙ n
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
  ⊢⦅⦆ᶜ-NeutralAt (lowerₑ _) n = lowerₙ n
  ⊢⦅⦆ᶜ-NeutralAt (∘ₑ _ _) n = ∘ₙ n
  ⊢⦅⦆ᶜ-NeutralAt (fstₑ _) n = fstₙ n
  ⊢⦅⦆ᶜ-NeutralAt (sndₑ _) n = sndₙ n
  ⊢⦅⦆ᶜ-NeutralAt (prodrecₑ _ _) n = prodrecₙ n
  ⊢⦅⦆ᶜ-NeutralAt (natrecₑ _ _) n = natrecₙ n
  ⊢⦅⦆ᶜ-NeutralAt (unitrecₑ _ _ x) n = unitrecₙ x n
  ⊢⦅⦆ᶜ-NeutralAt (emptyrecₑ _) n = emptyrecₙ n
  ⊢⦅⦆ᶜ-NeutralAt (Jₑ _ _) n = Jₙ n
  ⊢⦅⦆ᶜ-NeutralAt (Kₑ _ _ _) n = Kₙ n
  ⊢⦅⦆ᶜ-NeutralAt ([]-congₑ _ _) n = []-congₙ n
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
  -- matching type containing emptyrec p

  ⊢ˢemptyrec∉S :
    Consistent (ε » Δ) → Δ ⨾ H ⊢ S ⟨ t ⟩∷ A ↝ B → ε » Δ ⊢ t [ H ]ₕ ∷ A →
    emptyrec p ∈ S → ⊥
  ⊢ˢemptyrec∉S _          ε        _  ()
  ⊢ˢemptyrec∉S consistent (⊢c ∙ _) ⊢t here =
    case inversion-emptyrecₑ ⊢c of λ {
      (_ , PE.refl , _) →
    consistent _ ⊢t}
  ⊢ˢemptyrec∉S consistent (⊢c ∙ ⊢S) ⊢t (there d) =
    ⊢ˢemptyrec∉S consistent ⊢S (⊢⦅⦆ᶜ ⊢c ⊢t) d

opaque

  -- A version of the property above for well-typed states

  ⊢emptyrec∉S :
    Consistent (ε » Δ) → Δ ⊢ₛ ⟨ H , t , ρ , S ⟩ ∷ A → emptyrec p ∈ S → ⊥
  ⊢emptyrec∉S consistent (⊢ₛ _ ⊢t ⊢S) x = ⊢ˢemptyrec∉S consistent ⊢S ⊢t x

opaque

  -- A continuation's "hole type" is not definitionally equal to U l
  -- (given a certain assumption).

  hole-type-not-U :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    Δ ⨾ H ⊢ᶜ c ⟨ t ⟩∷ A ↝ B → ¬ ε » Γ ⊢ A ≡ U l
  hole-type-not-U (lowerₑ _)       = U≢Liftⱼ ∘→ sym
  hole-type-not-U (∘ₑ _ _)         = U≢ΠΣⱼ ∘→ sym
  hole-type-not-U (fstₑ _)         = U≢ΠΣⱼ ∘→ sym
  hole-type-not-U (sndₑ _)         = U≢ΠΣⱼ ∘→ sym
  hole-type-not-U (prodrecₑ _ _)   = U≢ΠΣⱼ ∘→ sym
  hole-type-not-U (natrecₑ _ _)    = U≢ℕ ∘→ sym
  hole-type-not-U (unitrecₑ _ _ _) = U≢Unitⱼ ∘→ sym
  hole-type-not-U (emptyrecₑ _)    = U≢Emptyⱼ ∘→ sym
  hole-type-not-U (Jₑ _ _)         = Id≢U
  hole-type-not-U (Kₑ _ _ _)       = Id≢U
  hole-type-not-U ([]-congₑ _ _)   = Id≢U
  hole-type-not-U (conv ⊢c _)      = hole-type-not-U ⊢c

private opaque

  -- A variant of ⊢∷→Names<.

  ⊢∷→Names<′ :
    {∇ : DCon (Term 0) n} →
    ∇ » Γ ⊢ wk ρ t [ σ ] ∷ A → Names< n t
  ⊢∷→Names<′ = Names<-wk→ ∘→ Names<-[]→ ∘→ ⊢∷→Names<

private opaque

  -- A variant of ⊢→Names<.

  ⊢→Names<′ :
    {∇ : DCon (Term 0) n} →
    ∇ » Γ ⊢ wk ρ A [ σ ] → Names< n A
  ⊢→Names<′ = Names<-wk→ ∘→ Names<-[]→ ∘→ ⊢→Names<

private opaque

  -- A variant of ⊢→Names<′.

  ⊢→Names<″ :
    {∇ : DCon (Term 0) n} →
    ∇ » Γ ⊢ (wk ρ A [ σ ]) [ σ′ ] → Names< n A
  ⊢→Names<″ = Names<-wk→ ∘→ Names<-[]→ ∘→ Names<-[]→ ∘→ ⊢→Names<

private opaque

  -- A variant of ⊢∷L→Names<

  ⊢∷L→Names<′ :
    {∇ : DCon (Term 0) n} →
    ∇ » Γ ⊢ wk ρ l [ σ ] ∷Level → Names< n l
  ⊢∷L→Names<′ = Names<-wk→ ∘→ Names<-[]→ ∘→ ⊢∷L→Names<

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

opaque

  -- If Δ ⨾ H ⊢ᶜ c ⟨ t ⟩∷ A ↝ B and ε » Δ ⊢ t [ H ]ₕ ∷ A hold, then No-namesᶜ c holds.

  ⊢ᶜ⟨⟩↝→No-nameᶜ :
    Δ ⨾ H ⊢ᶜ c ⟨ t ⟩∷ A ↝ B →
    ε » Δ ⊢ t [ H ]ₕ ∷ A →
    No-namesᶜ c
  ⊢ᶜ⟨⟩↝→No-nameᶜ (∘ₑ ⊢u _) _ =
    ∘ₑ (⊢∷→Names<′ ⊢u)
  ⊢ᶜ⟨⟩↝→No-nameᶜ (fstₑ _) _ =
    fstₑ
  ⊢ᶜ⟨⟩↝→No-nameᶜ (sndₑ _) _ =
    sndₑ
  ⊢ᶜ⟨⟩↝→No-nameᶜ (prodrecₑ ⊢u ⊢A) _ =
    prodrecₑ (⊢→Names<′ ⊢A) (⊢∷→Names<′ ⊢u)
  ⊢ᶜ⟨⟩↝→No-nameᶜ (natrecₑ ⊢z ⊢s) _ =
    natrecₑ (⊢→Names<″ (syntacticTerm ⊢z)) (⊢∷→Names<′ ⊢z) (⊢∷→Names<′ ⊢s)
  ⊢ᶜ⟨⟩↝→No-nameᶜ (unitrecₑ ⊢u ⊢A _) _ =
    unitrecₑ (⊢→Names<′ ⊢A) (⊢∷→Names<′ ⊢u)
  ⊢ᶜ⟨⟩↝→No-nameᶜ (emptyrecₑ ⊢A) _ =
    emptyrecₑ (⊢→Names<′ ⊢A)
  ⊢ᶜ⟨⟩↝→No-nameᶜ (Jₑ {A} {t} {v} ⊢u ⊢B) ⊢t =
    case ⊢→Names<′ {A = Id A t v} (syntacticTerm ⊢t) of λ {
      (Id nn-A nn-t nn-v) →
    Jₑ nn-A nn-t (⊢→Names<′ ⊢B) (⊢∷→Names<′ ⊢u) nn-v}
  ⊢ᶜ⟨⟩↝→No-nameᶜ (Kₑ {A} {t} ⊢u ⊢B _) _ =
    case ⊢→Names<′ {A = Id A t t} (⊢∙→⊢ (wf ⊢B)) of
      λ{ (Id nn-A nn-t _) →
    Kₑ nn-A nn-t (⊢→Names<′ ⊢B) (⊢∷→Names<′ ⊢u)}
  ⊢ᶜ⟨⟩↝→No-nameᶜ ([]-congₑ {A} {t} {u} _ ⊢l) ⊢t =
    case ⊢→Names<′ {A = Id A t u} (syntacticTerm ⊢t) of λ {
      (Id nn-A nn-t nn-u) →
    []-congₑ (⊢∷L→Names<′ ⊢l) nn-A nn-t nn-u}
  ⊢ᶜ⟨⟩↝→No-nameᶜ (lowerₑ _) ⊢t =
    lowerₑ
  ⊢ᶜ⟨⟩↝→No-nameᶜ (conv ⊢c x) ⊢t =
    ⊢ᶜ⟨⟩↝→No-nameᶜ ⊢c ⊢t

opaque

  -- If Δ ⨾ H ⊢ S ⟨ t ⟩∷ A ↝ B and ε » Δ ⊢ t [ H ]ₕ ∷ A hold, then No-namesˢ S holds.

  ⊢⟨⟩↝→No-nameˢ :
    Δ ⨾ H ⊢ S ⟨ t ⟩∷ A ↝ B →
    ε » Δ ⊢ t [ H ]ₕ ∷ A →
    No-namesˢ S
  ⊢⟨⟩↝→No-nameˢ ε _ = ε
  ⊢⟨⟩↝→No-nameˢ (⊢c ∙ ⊢S) ⊢t =
    ⊢ᶜ⟨⟩↝→No-nameᶜ ⊢c ⊢t ∙ ⊢⟨⟩↝→No-nameˢ ⊢S (⊢⦅⦆ᶜ ⊢c ⊢t)

opaque

  -- If Δ ⊢ₛ s ∷ A holds, then No-namesₛ s holds.

  ⊢ₛ→No-namesₛ : Δ ⊢ₛ s ∷ A → No-namesₛ s
  ⊢ₛ→No-namesₛ ⊢s@(⊢ₛ ⊢H ⊢t ⊢S) =
    ⊢ₛ→No-namesₛ′ ⊢s , ⊢⟨⟩↝→No-nameˢ ⊢S ⊢t
