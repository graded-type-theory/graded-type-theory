------------------------------------------------------------------------
-- Some properties related to typing and Erased that hold both with and
-- without η-equality.
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

import Graded.Modality
open import Definition.Typed.Restrictions
import Definition.Untyped hiding (_∷_; _[_])

module Graded.Derived.Erased.Typed
  {a} {M : Set a}
  (open Definition.Untyped M)
  (open Graded.Modality M)
  {𝕄 : Modality}
  (R : Type-restrictions 𝕄)
  where

open Modality 𝕄
open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Consequences.DerivedRules.Identity R
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Consequences.Substitution R
open import Definition.Typed.Consequences.Syntactic R
open import Definition.Typed.Properties R
open import Definition.Typed.Reasoning.Reduction R
open import Definition.Typed.Reasoning.Type R
open import Definition.Typed.RedSteps R
open import Definition.Typed.Weakening R

import Definition.Untyped M as U
open import Definition.Untyped.Identity 𝕄
open import Definition.Untyped.Properties M

import Graded.Derived.Erased.Eta.Typed R as Eta
import Graded.Derived.Erased.NoEta.Typed R as NoEta
import Graded.Derived.Erased.Typed.Primitive R as P
import Graded.Derived.Erased.Untyped 𝕄 as Erased

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality

private variable
  n                                                  : Nat
  Γ                                                  : Con Term _
  A A₁ A₂ B B₁ B₂ t t′ t₁ t₂ u u₁ u₂ v v₁ v₂ w w₁ w₂ : Term _
  σ                                                  : Subst _ _
  s                                                  : Strength

------------------------------------------------------------------------
-- Lemmas about Erased, [_] and erased

-- Some lemmas that are proved under the assumption that Erased is
-- allowed.

module _ (Erased-ok : Erased-allowed s) where

  open Erased s

  private module P′ = P Erased-ok

  -- A formation rule for Erased.

  Erasedⱼ : Γ ⊢ A → Γ ⊢ Erased A
  Erasedⱼ = P′.Erasedⱼ

  -- A corresponding congruence rule.

  Erased-cong :
    Γ ⊢ A ≡ B →
    Γ ⊢ Erased A ≡ Erased B
  Erased-cong A≡B = P′.Erased-cong ⊢A A≡B
    where
    ⊢A = syntacticEq A≡B .proj₁

  -- An introduction rule for U.

  Erasedⱼ-U : Γ ⊢ A ∷ U → Γ ⊢ Erased A ∷ U
  Erasedⱼ-U ⊢A∷U = P′.Erasedⱼ-U ⊢A ⊢A∷U
    where
    ⊢A = univ ⊢A∷U

  -- A corresponding congruence rule.

  Erased-cong-U :
    Γ ⊢ A ≡ B ∷ U →
    Γ ⊢ Erased A ≡ Erased B ∷ U
  Erased-cong-U A≡B = P′.Erased-cong-U ⊢A A≡B
    where
    ⊢A = univ (syntacticEqTerm A≡B .proj₂ .proj₁)

  -- An introduction rule for Erased.

  []ⱼ : Γ ⊢ t ∷ A → Γ ⊢ [ t ] ∷ Erased A
  []ⱼ ⊢t = P′.[]ⱼ ⊢A ⊢t
    where
    ⊢A = syntacticTerm ⊢t

  -- A corresponding congruence rule.

  []-cong′ :
    Γ ⊢ t ≡ u ∷ A → Γ ⊢ [ t ] ≡ [ u ] ∷ Erased A
  []-cong′ t≡u = P′.[]-cong′ ⊢A t≡u
    where
    ⊢A = syntacticEqTerm t≡u .proj₁

  opaque
    unfolding erased

    -- A β-rule for Erased.

    Erased-β :
      Γ ⊢ t ∷ A →
      Γ ⊢ erased A [ t ] ≡ t ∷ A
    Erased-β = case PE.singleton s of λ where
      (𝕤 , PE.refl) → Eta.Erased-β Erased-ok
      (𝕨 , PE.refl) → NoEta.Erased-β Erased-ok

module _ where

  open Erased

  opaque
    unfolding erased

    -- An elimination rule for Erased.

    erasedⱼ : Γ ⊢ t ∷ Erased s A → Γ ⊢ erased s A t ∷ A
    erasedⱼ {s} = case PE.singleton s of λ where
      (𝕤 , PE.refl) → Eta.erasedⱼ
      (𝕨 , PE.refl) → NoEta.erasedⱼ

  opaque
    unfolding erased

    -- A corresponding congruence rule.

    erased-cong :
      Γ ⊢ A ≡ B → Γ ⊢ t ≡ u ∷ Erased s A →
      Γ ⊢ erased s A t ≡ erased s B u ∷ A
    erased-cong {s} A≡B = case PE.singleton s of λ where
      (𝕤 , PE.refl) → Eta.erased-cong
      (𝕨 , PE.refl) → NoEta.erased-cong A≡B

------------------------------------------------------------------------
-- Lemmas related to substᵉ

-- The following lemmas are proved under the assumption that []-cong
-- is allowed.

module _ (ok : []-cong-allowed s) where

  open Erased s

  private opaque

    -- Some lemmas used below.

    Erased-ok : Erased-allowed s
    Erased-ok = []-cong→Erased ok

    [erased-0]↑[[]]₀≡[]₀ :
      Γ ∙ A ⊢ B →
      Γ ⊢ t ∷ A →
      Γ ⊢ B [ erased (wk1 A) (var x0) ]↑ [ [ t ] ]₀ ≡ B [ t ]₀
    [erased-0]↑[[]]₀≡[]₀ {A} {B} {t} ⊢B ⊢t =
      B [ erased (wk1 A) (var x0) ]↑ [ [ t ] ]₀  ≡⟨ []↑-[]₀ B ⟩⊢≡
      B [ erased (wk1 A) (var x0) [ [ t ] ]₀ ]₀  ≡⟨ PE.cong (B [_]₀) erased-[] ⟩⊢≡
      B [ erased (wk1 A [ [ t ] ]₀) [ t ] ]₀     ≡⟨ PE.cong (λ A → B [ erased A _ ]₀) $ wk1-sgSubst _ _ ⟩⊢≡
      B [ erased A [ t ] ]₀                      ≡⟨ substTypeEq (refl ⊢B) $ Erased-β Erased-ok ⊢t ⟩⊢∎
      B [ t ]₀                                   ∎

    ⊢[erased-0]↑ :
      Γ ∙ A ⊢ B →
      Γ ∙ Erased A ⊢ B [ erased (wk1 A) (var x0) ]↑
    ⊢[erased-0]↑ ⊢B =
      case wf ⊢B of λ {
        (⊢Γ ∙ ⊢A) →
      case Erasedⱼ Erased-ok ⊢A of λ
        ⊢Erased-A →
      substitution ⊢B
        ( wk1Subst′ ⊢Γ ⊢Γ ⊢Erased-A (idSubst′ ⊢Γ)
        , PE.subst (_⊢_∷_ _ _) (wk≡subst _ _)
            (erasedⱼ $ var₀ ⊢Erased-A)
        )
        (⊢→⊢∙ ⊢Erased-A) }

  opaque
    unfolding substᵉ

    -- A typing rule for substᵉ.

    ⊢substᵉ :
      Γ ∙ A ⊢ B →
      Γ ⊢ v ∷ Id A t u →
      Γ ⊢ w ∷ B [ t ]₀ →
      Γ ⊢ substᵉ A B t u v w ∷ B [ u ]₀
    ⊢substᵉ {A} {B} {u} ⊢B ⊢v ⊢w =
      case inversion-Id (syntacticTerm ⊢v) of λ
        (⊢A , ⊢t , ⊢u) →
      case wf ⊢A of λ
        ⊢Γ →
      case Erasedⱼ Erased-ok ⊢A of λ
        ⊢Erased-A →
      conv
        (⊢subst (⊢[erased-0]↑ ⊢B) ([]-congⱼ′ ok ⊢v)
           (conv ⊢w $ sym $ [erased-0]↑[[]]₀≡[]₀ ⊢B ⊢t))
        ([erased-0]↑[[]]₀≡[]₀ ⊢B ⊢u)

  opaque
    unfolding substᵉ

    -- A reduction rule for substᵉ.

    substᵉ-⇒*′ :
      Γ ∙ A ⊢ B →
      Γ ⊢ t ≡ t′ ∷ A →
      Γ ⊢ u ∷ B [ t ]₀ →
      Γ ⊢ substᵉ A B t t′ rfl u ⇒* u ∷ B [ t ]₀
    substᵉ-⇒*′ {A} {B} {t} {t′} {u} ⊢B t≡t′ ⊢u =
      case syntacticEqTerm t≡t′ of λ
        (_ , ⊢t , _) →
      case ⊢[erased-0]↑ ⊢B of λ
        ⊢B[]↑ →
      case []-cong′ Erased-ok t≡t′ of λ
        [t]≡[t′] →
      case [erased-0]↑[[]]₀≡[]₀ ⊢B ⊢t of λ
        ≡B[t]₀ →
      case conv ⊢u (sym ≡B[t]₀) of λ
        ⊢u →
      conv*
        (subst 𝟘 (Erased A) (B [ erased (wk1 A) (var x0) ]↑)
           [ t ] [ t′ ] ([]-cong s A t t′ rfl) u              ⇒⟨ conv (subst-subst ⊢B[]↑ ([]-cong-β-⇒ t≡t′ ok) ⊢u) $
                                                                 substTypeEq (refl ⊢B[]↑) (sym [t]≡[t′]) ⟩
         subst 𝟘 (Erased A) (B [ erased (wk1 A) (var x0) ]↑)
           [ t ] [ t′ ] rfl u                                 ⇒⟨ subst-⇒′ ⊢B[]↑ [t]≡[t′] ⊢u ⟩∎

         u                                                    ∎)
        ≡B[t]₀

  opaque

    -- Another reduction rule for substᵉ.

    substᵉ-⇒* :
      Γ ∙ A ⊢ B →
      Γ ⊢ t ∷ A →
      Γ ⊢ u ∷ B [ t ]₀ →
      Γ ⊢ substᵉ A B t t rfl u ⇒* u ∷ B [ t ]₀
    substᵉ-⇒* ⊢B ⊢t = substᵉ-⇒*′ ⊢B (refl ⊢t)

  opaque

    -- An equality rule for substᵉ.

    substᵉ-≡ :
      Γ ∙ A ⊢ B →
      Γ ⊢ t ∷ A →
      Γ ⊢ u ∷ B [ t ]₀ →
      Γ ⊢ substᵉ A B t t rfl u ≡ u ∷ B [ t ]₀
    substᵉ-≡ ⊢B ⊢t ⊢u =
      subset*Term (substᵉ-⇒* ⊢B ⊢t ⊢u)

  opaque
    unfolding substᵉ

    -- An equality rule for substᵉ.

    substᵉ-cong :
      Γ ⊢ A₁ ≡ A₂ →
      Γ ∙ A₁ ⊢ B₁ ≡ B₂ →
      Γ ⊢ t₁ ≡ t₂ ∷ A₁ →
      Γ ⊢ u₁ ≡ u₂ ∷ A₁ →
      Γ ⊢ v₁ ≡ v₂ ∷ Id A₁ t₁ u₁ →
      Γ ⊢ w₁ ≡ w₂ ∷ B₁ [ t₁ ]₀ →
      Γ ⊢ substᵉ A₁ B₁ t₁ u₁ v₁ w₁ ≡ substᵉ A₂ B₂ t₂ u₂ v₂ w₂ ∷
        B₁ [ u₁ ]₀
    substᵉ-cong A₁≡A₂ B₁≡B₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ w₁≡w₂ =
      case syntacticEq B₁≡B₂ of λ
        (⊢B₁ , _) →
      case syntacticEqTerm t₁≡t₂ of λ
        (⊢A₁ , ⊢t₁ , _) →
      case syntacticEqTerm u₁≡u₂ of λ
        (_ , ⊢u₁ , _) →
      case wf ⊢A₁ of λ
        ⊢Γ →
      case Erasedⱼ Erased-ok ⊢A₁ of λ
        ⊢Erased-A₁ →
      conv
        (subst-cong (Erased-cong Erased-ok A₁≡A₂)
           (substitutionEq B₁≡B₂
              ( substRefl (wk1Subst′ ⊢Γ ⊢Γ ⊢Erased-A₁ (idSubst′ ⊢Γ))
              , PE.subst (_⊢_≡_∷_ _ _ _) (wk≡subst _ _)
                  (erased-cong (wkEq₁ ⊢Erased-A₁ A₁≡A₂)
                     (refl $ var₀ ⊢Erased-A₁))
              )
              (⊢→⊢∙ ⊢Erased-A₁))
           ([]-cong′ Erased-ok t₁≡t₂)
           ([]-cong′ Erased-ok u₁≡u₂)
           ([]-cong-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ ok)
           (conv w₁≡w₂ $ sym $ [erased-0]↑[[]]₀≡[]₀ ⊢B₁ ⊢t₁))
        ([erased-0]↑[[]]₀≡[]₀ ⊢B₁ ⊢u₁)

  opaque
    unfolding substᵉ

    -- A reduction rule for substᵉ.

    substᵉ-subst :
      Γ ∙ A ⊢ B →
      Γ ⊢ v₁ ⇒ v₂ ∷ Id A t u →
      Γ ⊢ w ∷ B [ t ]₀ →
      Γ ⊢ substᵉ A B t u v₁ w ⇒ substᵉ A B t u v₂ w ∷ B [ u ]₀
    substᵉ-subst ⊢B v₁⇒v₂ ⊢w =
      case inversion-Id (syntacticEqTerm (subsetTerm v₁⇒v₂) .proj₁) of λ
        (_ , ⊢t , ⊢u) →
      conv
        (subst-subst (⊢[erased-0]↑ ⊢B) ([]-cong-subst′ v₁⇒v₂ ok)
           (conv ⊢w $ sym $ [erased-0]↑[[]]₀≡[]₀ ⊢B ⊢t))
        ([erased-0]↑[[]]₀≡[]₀ ⊢B ⊢u)
