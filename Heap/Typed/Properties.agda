------------------------------------------------------------------------
-- Properties of stack and eliminator typing
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

open import Graded.Modality
open import Definition.Typed.Restrictions
open import Tools.Bool

module Heap.Typed.Properties
  {a} {M : Set a} {𝕄 : Modality M}
  (TR : Type-restrictions 𝕄)
  (ℕ-fullred : Bool)
  where

open Type-restrictions TR

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M
open import Definition.Typed TR
open import Definition.Typed.Properties TR
open import Definition.Typed.Consequences.DerivedRules TR
open import Definition.Typed.Consequences.Inversion TR
open import Definition.Typed.Consequences.Substitution TR
open import Definition.Typed.Consequences.Syntactic TR

open import Heap.Typed TR ℕ-fullred
open import Heap.Untyped 𝕄 type-variant
open import Heap.Untyped.Properties 𝕄 type-variant

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
  e : Elim _
  S : Stack _
  s : State _ _ _
  x : Fin _

opaque

  -- Typing of erased heaps

  ⊢erasedHeap : ∀ {n} {Δ : Con Term n} → ⊢ Δ → Δ ⊢ʰ erasedHeap n ∷ Δ
  ⊢erasedHeap {0} {(ε)} ⊢Δ = ε
  ⊢erasedHeap {1+ n} {(Δ ∙ A)} (⊢Δ ∙ ⊢A) =
    PE.subst (λ x → Δ ∙ x ⊢ʰ _ ∷ Δ ∙ A)
      (erasedHeap-subst A)
      (⊢erasedHeap ⊢Δ ∙● ⊢A)

opaque

 -- Typing of the initial state

  ⊢initial : Δ ⊢ t ∷ A → Δ ⨾ Δ ⊢ initial t ∷ A
  ⊢initial {Δ} {t} {A} ⊢t =
    A , ⊢erasedHeap (wfTerm ⊢t)
      , PE.subst (Δ ⊢_∷ _) (lemma t) ⊢t
      , ε
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
  ⊢⦅⦆ᵉ (fstₑ _ _) ⊢t =
    fstⱼ′ ⊢t
  ⊢⦅⦆ᵉ (sndₑ _ _) ⊢t =
    sndⱼ′ ⊢t
  ⊢⦅⦆ᵉ (prodrecₑ ⊢u ⊢A) ⊢t =
    prodrecⱼ′ ⊢A ⊢t ⊢u
  ⊢⦅⦆ᵉ (natrecₑ ⊢z ⊢s ⊢A) ⊢t =
    natrecⱼ ⊢A ⊢z ⊢s ⊢t
  ⊢⦅⦆ᵉ (unitrecₑ ⊢u ⊢A no-η) ⊢t =
    unitrecⱼ′ ⊢A ⊢t ⊢u
  ⊢⦅⦆ᵉ (Jₑ ⊢u ⊢B) ⊢t =
    Jⱼ′ ⊢B ⊢u ⊢t
  ⊢⦅⦆ᵉ (Kₑ ⊢u ⊢B ok) ⊢t =
    Kⱼ′ ⊢B ⊢u ⊢t ok
  ⊢⦅⦆ᵉ ([]-congₑ ok) ⊢t =
    []-congⱼ′ ok ⊢t
  ⊢⦅⦆ᵉ sucₑ ⊢t =
    sucⱼ ⊢t
  ⊢⦅⦆ᵉ (conv ⊢e B≡B′) ⊢t =
    conv (⊢⦅⦆ᵉ ⊢e ⊢t) B≡B′

-- opaque

--   -- An inverse of the above property

--   ⊢⦅⦆ᵉ⁻¹ : ⦃ T ℕ-fullred ⦄
--          → Δ ⊢ ⦅ e ⦆ᵉ t [ H ]ₕ ∷ B
--          → ∃ λ A → Δ ⨾ H ⊢ᵉ e ⟨ t ⟩∷ A ↝ B × Δ ⊢ t [ H ]ₕ ∷ A
--   ⊢⦅⦆ᵉ⁻¹ {e = ∘ₑ p u E} ⊢et =
--     case inversion-app ⊢et of λ
--       (F , G , q , ⊢t , ⊢u , B≡Gu) →
--     case syntacticΠ (syntacticTerm ⊢t) of λ
--       (⊢F , ⊢G) →
--     _ , conv (∘ₑ ⊢u ⊢G) (sym B≡Gu) , ⊢t
--   ⊢⦅⦆ᵉ⁻¹ {e = fstₑ p} ⊢et =
--     case inversion-fst ⊢et of λ
--       (F , G , q , ⊢F , ⊢G , ⊢t , B≡F) →
--     _ , conv (fstₑ ⊢F ⊢G) (sym B≡F) , ⊢t
--   ⊢⦅⦆ᵉ⁻¹ {e = sndₑ p} ⊢et =
--     case inversion-snd ⊢et of λ
--       (F , G , q , ⊢F , ⊢G , ⊢t , B≡Gt) →
--     _ , conv (sndₑ ⊢F ⊢G) (sym B≡Gt) , ⊢t
--   ⊢⦅⦆ᵉ⁻¹ {e = prodrecₑ r p q A u E} ⊢et =
--     case inversion-prodrec ⊢et of λ
--       (F , G , q , ⊢F , ⊢G , ⊢A , ⊢t , ⊢u , B≡At) →
--     _ , conv (prodrecₑ ⊢u ⊢A) (sym B≡At) , ⊢t
--   ⊢⦅⦆ᵉ⁻¹ {e = natrecₑ p q r A z s E} ⊢et =
--     case inversion-natrec ⊢et of λ
--       (⊢A , ⊢z , ⊢s , ⊢t , B≡) →
--     _ , conv (natrecₑ ⊢z ⊢s ⊢A) (sym B≡) , ⊢t
--   ⊢⦅⦆ᵉ⁻¹ {e = unitrecₑ p q A u E} ⊢et =
--     case inversion-unitrec ⊢et of λ
--       (⊢A , ⊢t , ⊢u , B≡At) →
--     _ , conv (unitrecₑ ⊢u ⊢A {!!}) (sym B≡At) , ⊢t
--   ⊢⦅⦆ᵉ⁻¹ {e = Jₑ p q A t B u v E} ⊢et =
--     case inversion-J ⊢et of λ
--       (_ , _ , ⊢B , ⊢u , _ , ⊢w , C≡B₊) →
--     _ , conv (Jₑ ⊢u ⊢B) (sym C≡B₊) , ⊢w
--   ⊢⦅⦆ᵉ⁻¹ {e = Kₑ p A t B u E} ⊢et =
--     case inversion-K ⊢et of λ
--       (_ , _ , ⊢B , ⊢u , ⊢v , ok , C≡B₊) →
--     _ , conv (Kₑ ⊢u ⊢B ok) (sym C≡B₊) , ⊢v
--   ⊢⦅⦆ᵉ⁻¹ {e = []-congₑ s A t u E} ⊢et =
--     case inversion-[]-cong ⊢et of λ
--       (_ , _ , _ , ⊢v , ok , B≡Id) →
--     _ , conv ([]-congₑ ok) (sym B≡Id) , ⊢v
--   ⊢⦅⦆ᵉ⁻¹ {e = sucₑ} ⊢et =
--     case inversion-suc ⊢et of λ
--       (⊢t , B≡ℕ) →
--     _ , conv sucₑ (sym B≡ℕ) , ⊢t

opaque

  -- Well-typed terms applied to well-typed stacks are
  -- well-typed under a heap substitution.

  ⊢⦅⦆ : Δ ⨾ H ⊢ S ⟨ t ⟩∷ A ↝ B
     → Δ ⊢ t [ H ]ₕ ∷ A
     → Δ ⊢ ⦅ S ⦆ t [ H ]ₕ ∷ B
  ⊢⦅⦆ ε ⊢t = ⊢t
  ⊢⦅⦆ {H} {S = e ∙ S} {t} (⊢e ∙ ⊢S) ⊢t =
    ⊢⦅⦆ ⊢S (⊢⦅⦆ᵉ ⊢e ⊢t)

-- opaque

--   -- An inverse of the above property

--   ⊢⦅⦆⁻¹ : ⦃ T ℕ-fullred ⦄
--        → ε ⊢ ⦅ S ⦆ t [ H ]ₕ ∷ B
--        → ∃ λ A → H ⊢ S ⟨ t ⟩∷ A ↝ B × ε ⊢ t [ H ]ₕ ∷ A
--   ⊢⦅⦆⁻¹ {S = ε} ⊢St =
--     _ , ε , ⊢St
--   ⊢⦅⦆⁻¹ {S = e ∙ S} ⊢St =
--     case ⊢⦅⦆⁻¹ {S = S} ⊢St of λ
--       (_ , ⊢S , ⊢et) →
--     case ⊢⦅⦆ᵉ⁻¹ ⊢et of λ
--       (_ , ⊢e , ⊢t) →
--     _ , ⊢e ∙ ⊢S , ⊢t

opaque

  -- Equal terms are equal when applied to eliminators under
  -- heap substitutions.

  ⊢⦅⦆ᵉ-cong : Δ ⨾ H ⊢ᵉ e ⟨ t ⟩∷ A ↝ B
           → Δ ⊢ t [ H ]ₕ ≡ u [ H ]ₕ ∷ A
           → Δ ⊢ ⦅ e ⦆ᵉ t [ H ]ₕ ≡ ⦅ e ⦆ᵉ u [ H ]ₕ ∷ B
  ⊢⦅⦆ᵉ-cong (∘ₑ ⊢u _) t≡u =
    app-cong t≡u (refl ⊢u)
  ⊢⦅⦆ᵉ-cong (fstₑ _ _) t≡u =
    fst-cong′ t≡u
  ⊢⦅⦆ᵉ-cong (sndₑ _ _) t≡u =
    snd-cong′ t≡u
  ⊢⦅⦆ᵉ-cong (prodrecₑ ⊢v ⊢A) t≡u =
    prodrec-cong′ (refl ⊢A) t≡u (refl ⊢v)
  ⊢⦅⦆ᵉ-cong (natrecₑ ⊢z ⊢s ⊢A) t≡u =
    natrec-cong′ (refl ⊢A) (refl ⊢z) (refl ⊢s) t≡u
  ⊢⦅⦆ᵉ-cong (unitrecₑ ⊢v ⊢A no-η) t≡u =
    unitrec-cong′ (refl ⊢A) t≡u (refl ⊢v)
  ⊢⦅⦆ᵉ-cong (Jₑ ⊢u ⊢B) t≡u =
    case inversion-Id (syntacticEqTerm t≡u .proj₁) of λ
      (⊢A , ⊢t , ⊢v) →
    J-cong′ (refl ⊢A) (refl ⊢t) (refl ⊢B) (refl ⊢u) (refl ⊢v) t≡u
  ⊢⦅⦆ᵉ-cong (Kₑ ⊢u ⊢B ok) t≡u =
    case inversion-Id (syntacticEqTerm t≡u .proj₁) of λ
      (⊢A , ⊢t , _) →
    K-cong′ (refl ⊢A) (refl ⊢t) (refl ⊢B) (refl ⊢u) t≡u ok
  ⊢⦅⦆ᵉ-cong ([]-congₑ ok) t≡u =
    case inversion-Id (syntacticEqTerm t≡u .proj₁) of λ
      (⊢A , ⊢t , ⊢u) →
    []-cong-cong (refl ⊢A) (refl ⊢t) (refl ⊢u) t≡u ok
  ⊢⦅⦆ᵉ-cong sucₑ t≡u =
    suc-cong t≡u
  ⊢⦅⦆ᵉ-cong (conv ⊢e B≡B′) t≡u =
    conv (⊢⦅⦆ᵉ-cong ⊢e t≡u) B≡B′

opaque

  -- Equal terms are equal when applied to stacks under
  -- heap substitutions.

  ⊢⦅⦆-cong : Δ ⨾ H ⊢ S ⟨ t ⟩∷ A ↝ B
          → Δ ⊢ t [ H ]ₕ ≡ u [ H ]ₕ ∷ A
          → Δ ⊢ ⦅ S ⦆ t [ H ]ₕ ≡ ⦅ S ⦆ u [ H ]ₕ ∷ B
  ⊢⦅⦆-cong ε t≡u = t≡u
  ⊢⦅⦆-cong {H} {S = e ∙ S} (⊢e ∙ ⊢S) t≡u =
    ⊢⦅⦆-cong ⊢S (⊢⦅⦆ᵉ-cong ⊢e t≡u)

opaque

  -- Applying terms to eliminators respects reduction

  ⊢⦅⦆ᵉ-subst : ⦃ T (not ℕ-fullred) ⦄
            → Δ ⨾ H ⊢ᵉ e ⟨ t ⟩∷ A ↝ B
            → Δ ⊢ t [ H ]ₕ ⇒ u [ H ]ₕ ∷ A
            → Δ ⊢ ⦅ e ⦆ᵉ t [ H ]ₕ ⇒ ⦅ e ⦆ᵉ u [ H ]ₕ ∷ B
  ⊢⦅⦆ᵉ-subst (∘ₑ ⊢u _) d =
    app-subst d ⊢u
  ⊢⦅⦆ᵉ-subst (fstₑ _ _) d =
    fst-subst′ d
  ⊢⦅⦆ᵉ-subst (sndₑ _ _) d =
    snd-subst′ d
  ⊢⦅⦆ᵉ-subst (prodrecₑ ⊢u ⊢A) d =
    prodrec-subst′ ⊢A ⊢u d
  ⊢⦅⦆ᵉ-subst (natrecₑ ⊢z ⊢s ⊢A) d =
    natrec-subst ⊢A ⊢z ⊢s d
  ⊢⦅⦆ᵉ-subst (unitrecₑ ⊢u ⊢A no-η) d =
    unitrec-subst′ ⊢A ⊢u d no-η
  ⊢⦅⦆ᵉ-subst (Jₑ ⊢u ⊢B) d =
    J-subst′ ⊢B ⊢u d
  ⊢⦅⦆ᵉ-subst (Kₑ ⊢u ⊢B ok) d =
    K-subst′ ⊢B ⊢u d ok
  ⊢⦅⦆ᵉ-subst ([]-congₑ ok) d =
    []-cong-subst′ d ok
  ⊢⦅⦆ᵉ-subst ⦃ (fr) ⦄ (sucₑ ⦃ (¬fr) ⦄) d =
    ⊥-elim (not-T-and-¬T′ ℕ-fullred)
  ⊢⦅⦆ᵉ-subst (conv ⊢e B≡B′) d =
    conv (⊢⦅⦆ᵉ-subst ⊢e d) B≡B′

opaque

  -- Applying terms to stacks respects reduction

  ⊢⦅⦆-subst : ⦃ T (not ℕ-fullred) ⦄
           → Δ ⨾ H ⊢ S ⟨ t ⟩∷ A ↝ B
           → Δ ⊢ (t [ H ]ₕ) ⇒ (u [ H ]ₕ) ∷ A
           → Δ ⊢ ⦅ S ⦆ t [ H ]ₕ ⇒ ⦅ S ⦆ u [ H ]ₕ ∷ B
  ⊢⦅⦆-subst ε d = d
  ⊢⦅⦆-subst (⊢e ∙ ⊢S) d =
    ⊢⦅⦆-subst ⊢S (⊢⦅⦆ᵉ-subst ⊢e d)

opaque

  -- Conversion of the head term in eliminator typing

  ⊢ᵉ-convₜ : Δ ⨾ H ⊢ᵉ e ⟨ t ⟩∷ A ↝ B
           → Δ ⊢ t [ H ]ₕ ≡ u [ H ]ₕ ∷ A
           → Δ ⨾ H ⊢ᵉ e ⟨ u ⟩∷ A ↝ B
  ⊢ᵉ-convₜ (∘ₑ {A} {B} ⊢v ⊢B) t≡u =
    ∘ₑ {A = A} {B} ⊢v ⊢B
  ⊢ᵉ-convₜ (fstₑ ⊢A ⊢B) t≡u =
    fstₑ ⊢A ⊢B
  ⊢ᵉ-convₜ (sndₑ ⊢A ⊢B) t≡u =
    conv (sndₑ ⊢A ⊢B)
      (substTypeEq (refl ⊢B) (fst-cong′ (sym t≡u)))
  ⊢ᵉ-convₜ (prodrecₑ {B} {C} ⊢v ⊢A) t≡u =
    conv (prodrecₑ {B = B} {C} ⊢v ⊢A)
      (substTypeEq (refl ⊢A) (sym t≡u))
  ⊢ᵉ-convₜ (natrecₑ ⊢z ⊢s ⊢A) t≡u =
    conv (natrecₑ ⊢z ⊢s ⊢A)
      (substTypeEq (refl ⊢A) (sym t≡u))
  ⊢ᵉ-convₜ (unitrecₑ ⊢v ⊢A no-η) t≡u =
    conv (unitrecₑ ⊢v ⊢A no-η)
      (substTypeEq (refl ⊢A) (sym t≡u))
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
      (substTypeEq₂ (refl ⊢B) (refl ⊢v) (sym t≡u′))
  ⊢ᵉ-convₜ {H} {t} {u} (Kₑ ⊢u ⊢B ok) t≡u =
    conv (Kₑ ⊢u ⊢B ok)
      (substTypeEq (refl ⊢B) (sym t≡u))
  ⊢ᵉ-convₜ {H} {t} {u} ([]-congₑ ok) t≡u =
    []-congₑ ok
  ⊢ᵉ-convₜ sucₑ t≡u =
    sucₑ
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

  ⊢whnf⦅⦆ᵉ : ⦃ T (not ℕ-fullred) ⦄
          → Δ ⨾ H ⊢ᵉ e ⟨ u ⟩∷ A ↝ B
          → ¬ Neutral t
          → ¬ Whnf (⦅ e ⦆ᵉ t)
  ⊢whnf⦅⦆ᵉ (∘ₑ _ _) ¬n (ne (∘ₙ n)) = ¬n n
  ⊢whnf⦅⦆ᵉ (fstₑ _ _) ¬n (ne (fstₙ n)) = ¬n n
  ⊢whnf⦅⦆ᵉ (sndₑ _ _) ¬n (ne (sndₙ n)) = ¬n n
  ⊢whnf⦅⦆ᵉ (prodrecₑ _ _) ¬n (ne (prodrecₙ n)) = ¬n n
  ⊢whnf⦅⦆ᵉ (natrecₑ _ _ _) ¬n (ne (natrecₙ n)) = ¬n n
  ⊢whnf⦅⦆ᵉ (unitrecₑ _ _ _) ¬n (ne (unitrecₙ _ n)) = ¬n n
  ⊢whnf⦅⦆ᵉ (Jₑ _ _) ¬n (ne (Jₙ n)) = ¬n n
  ⊢whnf⦅⦆ᵉ (Kₑ _ _ _) ¬n (ne (Kₙ n)) = ¬n n
  ⊢whnf⦅⦆ᵉ ([]-congₑ _) ¬n (ne ([]-congₙ n)) = ¬n n
  ⊢whnf⦅⦆ᵉ sucₑ ¬n w = not-T-and-¬T′ ℕ-fullred
  ⊢whnf⦅⦆ᵉ (conv ⊢e x) ¬n w = ⊢whnf⦅⦆ᵉ ⊢e ¬n w

opaque

  ⊢whnf⦅⦆ : ⦃ T (not ℕ-fullred) ⦄
         → Δ ⨾ H ⊢ e ∙ S ⟨ u ⟩∷ A ↝ B
         → ¬ Neutral t
         → ¬ Whnf (⦅ e ∙ S ⦆ t)
  ⊢whnf⦅⦆ (⊢e ∙ ε) n w = ⊢whnf⦅⦆ᵉ ⊢e n w
  ⊢whnf⦅⦆ {e} (⊢e ∙ (⊢e′ ∙ ⊢S)) n w =
    ⊢whnf⦅⦆ (⊢e′ ∙ ⊢S) (¬⦅⦆ᵉ-neutral e n) w

opaque

  ⊢⦅⦆ᵉ-NeutralAt : ⦃ T (not ℕ-fullred) ⦄
                → Δ ⨾ H ⊢ᵉ e ⟨ t ⟩∷ A ↝ B
                → NeutralAt x t
                → NeutralAt x (⦅ e ⦆ᵉ t)
  ⊢⦅⦆ᵉ-NeutralAt (∘ₑ _ _) n = ∘ₙ n
  ⊢⦅⦆ᵉ-NeutralAt (fstₑ _ _) n = fstₙ n
  ⊢⦅⦆ᵉ-NeutralAt (sndₑ _ _) n = sndₙ n
  ⊢⦅⦆ᵉ-NeutralAt (prodrecₑ _ _) n = prodrecₙ n
  ⊢⦅⦆ᵉ-NeutralAt (natrecₑ _ _ _) n = natrecₙ n
  ⊢⦅⦆ᵉ-NeutralAt (unitrecₑ _ _ x) n = unitrecₙ x n
  ⊢⦅⦆ᵉ-NeutralAt (Jₑ _ _) n = Jₙ n
  ⊢⦅⦆ᵉ-NeutralAt (Kₑ _ _ _) n = Kₙ n
  ⊢⦅⦆ᵉ-NeutralAt ([]-congₑ _) n = []-congₙ n
  ⊢⦅⦆ᵉ-NeutralAt sucₑ n = ⊥-elim (not-T-and-¬T′ ℕ-fullred)
  ⊢⦅⦆ᵉ-NeutralAt (conv ⊢e x) n = ⊢⦅⦆ᵉ-NeutralAt ⊢e n

opaque

  ⊢⦅⦆-NeutralAt : ⦃ T (not ℕ-fullred) ⦄
               → Δ ⨾ H ⊢ S ⟨ t ⟩∷ A ↝ B
               → NeutralAt x t
               → NeutralAt x (⦅ S ⦆ t)
  ⊢⦅⦆-NeutralAt ε n = n
  ⊢⦅⦆-NeutralAt (⊢e ∙ ⊢S) n = ⊢⦅⦆-NeutralAt ⊢S (⊢⦅⦆ᵉ-NeutralAt ⊢e n)
