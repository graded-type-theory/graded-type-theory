------------------------------------------------------------------------
-- Some properties related to typing and Erased that hold both with and
-- without η-equality.
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

import Graded.Modality
open import Definition.Typed.Restrictions
import Definition.Untyped
  hiding (_∷_; _[_]) renaming (_[_,_] to _[_,_]₁₀)

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
open import Definition.Typed.Consequences.DerivedRules R
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Consequences.Substitution R
open import Definition.Typed.Consequences.Syntactic R
open import Definition.Typed.Properties R
open import Definition.Typed.Reasoning.Reduction R
open import Definition.Typed.Reasoning.Type R
open import Definition.Typed.RedSteps R
open import Definition.Typed.Weakening R as W

import Definition.Untyped M as U
open import Definition.Untyped.Identity 𝕄
open import Definition.Untyped.Properties M
open import Definition.Untyped.Sigma 𝕄

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
open import Tools.Relation

private variable
  n                                                    : Nat
  Γ                                                    : Con Term _
  A A₁ A₂ B B₁ B₂ C t t′ t₁ t₂ u u₁ u₂ v v₁ v₂ w w₁ w₂ : Term _
  σ                                                    : Subst _ _
  s                                                    : Strength

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
-- Lemmas proved under the assumption that []-cong is allowed

module _ (ok : []-cong-allowed s) where

  open Erased s

  private opaque

    -- Some lemmas used below.

    Erased-ok : Erased-allowed s
    Erased-ok = []-cong→Erased ok

    Σ-ok : Σ-allowed s 𝟘 𝟘
    Σ-ok = Erased-ok .proj₂

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

  ----------------------------------------------------------------------
  -- Lemmas related to substᵉ

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

  ----------------------------------------------------------------------
  -- Lemmas related to Jᵉ

  private

    -- A definition used below.

    Singleton : Term n → Term n → Term n
    Singleton A t = Σ⟨ s ⟩ 𝟘 , 𝟘 ▷ A ▹ Id (wk1 A) (wk1 t) (var x0)

  private opaque

    -- Some lemmas used below.

    lemma₁ :
      wk₂ t PE.≡ U.wk (lift (step (step id))) (wk1 t) [ u ]₀
    lemma₁ {t} {u} =
      wk₂ t                                                  ≡⟨ wk≡subst _ _ ⟩
      t U.[ sgSubst u ₛ• lift (step (step id)) ₛ• step id ]  ≡˘⟨ subst-wk t ⟩
      wk1 t U.[ sgSubst u ₛ• lift (step (step id)) ]         ≡˘⟨ subst-wk (wk1 t) ⟩
      U.wk (lift (step (step id))) (wk1 t) [ u ]₀            ∎

    lemma₂ :
      wk2 t PE.≡ U.wk (lift (step (step id))) (wk1 t) [ u ]₀
    lemma₂ {t} {u} =
      wk2 t                                        ≡⟨ wk2≡wk₂ ⟩
      wk₂ t                                        ≡⟨ lemma₁ ⟩
      U.wk (lift (step (step id))) (wk1 t) [ u ]₀  ∎

    lemma₃ :
      U.wk (lift (step (step id))) t
        U.[ liftSubst (consSubst (sgSubst u) v) ] PE.≡
      t
    lemma₃ {t} {u} {v} =
      U.wk (lift (step (step id))) t
        U.[ liftSubst (consSubst (sgSubst u) v) ]                    ≡⟨ subst-wk t ⟩

      t U.[ liftSubst (consSubst (sgSubst u) v) ₛ•
            lift (step (step id)) ]                                  ≡⟨ subst-lift-ₛ• t ⟩

      t U.[ liftSubst (consSubst (sgSubst u) v ₛ• step (step id)) ]  ≡⟨⟩

      t U.[ liftSubst idSubst ]                                      ≡⟨ substVar-to-subst subst-lift-id t ⟩

      t U.[ idSubst ]                                                ≡⟨ subst-id _ ⟩

      t                                                              ∎

    lemma₄ :
      ∀ t → wk₂ t [ u ]₀ PE.≡ wk1 t U.[ consSubst (wk1Subst idSubst) v ]
    lemma₄ {u} {v} t =
      wk₂ t [ u ]₀                                ≡⟨ subst-wk t ⟩
      t U.[ wk1Subst idSubst ]                    ≡˘⟨ wk1-tail t ⟩
      wk1 t U.[ consSubst (wk1Subst idSubst) v ]  ∎

    lemma₅ :
      wk₂ t U.[ liftSubst (sgSubst u) ] PE.≡ wk1 t
    lemma₅ {t} {u} =
      wk₂ t U.[ liftSubst (sgSubst u) ]                ≡⟨ subst-wk t ⟩
      t U.[ liftSubst (sgSubst u) ₛ• step (step id) ]  ≡⟨⟩
      t U.[ tail idSubst ]                             ≡˘⟨ wk1-tailId _ ⟩
      wk1 t                                            ∎

    lemma₆ :
      Γ ⊢ A₁ ≡ A₂ →
      Γ ⊢ t₁ ≡ t₂ ∷ A₁ →
      Γ ∙ A₁ ∙ Id (wk1 A₁) (wk1 t₁) (var x0) ⊢
        Id (wk₂ (Singleton A₁ t₁)) (wk₂ (prod s 𝟘 t₁ rfl))
          (prod s 𝟘 (var x1) (var x0)) ≡
        Id (wk₂ (Singleton A₂ t₂)) (wk₂ (prod s 𝟘 t₂ rfl))
          (prod s 𝟘 (var x1) (var x0))
    lemma₆ A₁≡A₂ t₁≡t₂ =
      case syntacticEqTerm t₁≡t₂ of λ
        (⊢A₁ , ⊢t₁ , _) →
      case W.wk (step (step id)) (⊢→⊢∙ (J-motive-context-type ⊢t₁))
             ⊢A₁ of λ
        ⊢A₁′ →
      Id-cong
        (ΠΣ-cong′
           (wkEq (step (step id)) (⊢→⊢∙ (J-motive-context-type ⊢t₁))
              A₁≡A₂)
           (Id-cong
              (wkEq (lift (step (step id))) (⊢→⊢∙ ⊢A₁′)
                 (wkEq₁ ⊢A₁ A₁≡A₂))
              (wkEqTerm (lift (step (step id))) (⊢→⊢∙ ⊢A₁′)
                 (wkEqTerm₁ ⊢A₁ t₁≡t₂))
              (_⊢_≡_∷_.refl $
               PE.subst (_⊢_∷_ _ _) (wk1-wk≡lift-wk1 _ _) $
               var₀ ⊢A₁′))
           Σ-ok)
        (prod-cong′
           (W.wk (lift (step (step id))) (⊢→⊢∙ ⊢A₁′)
              (J-motive-context-type ⊢t₁))
           (wkEqTerm (step (step id)) (⊢→⊢∙ (J-motive-context-type ⊢t₁))
              t₁≡t₂)
           (_⊢_≡_∷_.refl $
            PE.subst (_⊢_∷_ _ _)
              (PE.cong₃ Id lemma₁ lemma₁ PE.refl) $
            rflⱼ $
            wkTerm (step (step id)) (⊢→⊢∙ (J-motive-context-type ⊢t₁))
              ⊢t₁)
           Σ-ok)
        (prod-cong′
           (W.wk (lift (step (step id))) (⊢→⊢∙ ⊢A₁′)
              (J-motive-context-type ⊢t₁))
           (_⊢_≡_∷_.refl $
            PE.subst (_⊢_∷_ _ _) wk2≡wk₂ $
            var₁ (J-motive-context-type ⊢t₁))
           (_⊢_≡_∷_.refl $
            PE.subst (_⊢_∷_ _ _)
              (PE.cong₃ Id lemma₂ lemma₂ PE.refl) $
            var₀ (J-motive-context-type ⊢t₁))
           Σ-ok)

    lemma₆′ :
      Γ ⊢ t ∷ A →
      Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊢
        Id (wk₂ (Singleton A t)) (wk₂ (prod s 𝟘 t rfl))
          (prod s 𝟘 (var x1) (var x0))
    lemma₆′ ⊢t =
      case syntacticTerm ⊢t of λ
        ⊢A →
      syntacticEq (lemma₆ (refl ⊢A) (refl ⊢t)) .proj₁

    lemma₇ :
      Γ ⊢ t ∷ A →
      Γ ⊢ rfl ∷
        Id (wk₂ (Singleton A t)) (wk₂ (prod s 𝟘 t rfl))
          (prod s 𝟘 (var x1) (var x0))
        [ t , rfl ]₁₀
    lemma₇ ⊢t =
      PE.subst (_⊢_∷_ _ _)
        (PE.sym $ PE.cong₃ Id
           (PE.cong₂ (Σ⟨_⟩_,_▷_▹_ s 𝟘 𝟘) wk₂-[,] $
            PE.cong₃ Id lemma₃ lemma₃ PE.refl)
           (PE.cong₂ (prod s 𝟘) wk₂-[,] PE.refl)
           PE.refl) $
      rflⱼ $
      ⊢prod (J-motive-context-type ⊢t) ⊢t
        (PE.subst (_⊢_∷_ _ _)
           (PE.sym $ PE.cong₃ Id
              (wk1-sgSubst _ _)
              (wk1-sgSubst _ _)
              PE.refl) $
         rflⱼ ⊢t)
        Σ-ok

    lemma₈ :
      Γ ⊢ A₁ ≡ A₂ →
      Γ ∙ A₁ ∙ Id (wk1 A₁) (wk1 t₁) (var x0) ⊢ B₁ ≡ B₂ →
      Γ ⊢ t₁ ≡ t₂ ∷ A₁ →
      Γ ∙ Singleton A₁ t₁ ⊢
        B₁ U.[ consSubst
                 (consSubst (wk1Subst idSubst)
                    (fst⟨ s ⟩ 𝟘 (wk1 A₁) (var x0)))
                 (snd⟨ s ⟩ 𝟘 𝟘 (wk1 A₁) (Id (wk₂ A₁) (wk₂ t₁) (var x0))
                    (var x0))
             ] ≡
        B₂ U.[ consSubst
                 (consSubst (wk1Subst idSubst)
                    (fst⟨ s ⟩ 𝟘 (wk1 A₂) (var x0)))
                 (snd⟨ s ⟩ 𝟘 𝟘 (wk1 A₂) (Id (wk₂ A₂) (wk₂ t₂) (var x0))
                    (var x0))
             ]
    lemma₈ {A₁} {t₁} A₁≡A₂ B₁≡B₂ t₁≡t₂ =
      case syntacticEqTerm t₁≡t₂ of λ
        (⊢A₁ , ⊢t₁ , _) →
      case wf ⊢A₁ of λ
        ⊢Γ →
      case ΠΣⱼ′ (Idⱼ (wkTerm₁ ⊢A₁ ⊢t₁) (var₀ ⊢A₁)) Σ-ok of λ
        ⊢Singleton₁ →
      case wkEq₁ ⊢Singleton₁ A₁≡A₂ of λ
        A₁≡A₂′ →
      case syntacticEq A₁≡A₂′ of λ
        (⊢A₁′ , _) →
      substitutionEq B₁≡B₂
        ( ( substRefl (wk1Subst′ ⊢Γ ⊢Γ ⊢Singleton₁ (idSubst′ ⊢Γ))
          , PE.subst (_⊢_≡_∷_ _ _ _) (wk1-tailId _)
              (fst⟨⟩-cong A₁≡A₂′ $
               refl (var₀ ⊢Singleton₁))
          )
        , PE.subst (_⊢_≡_∷_ _ _ _)
            (PE.cong₃ Id (lemma₄ A₁) (lemma₄ t₁) PE.refl)
            (snd⟨⟩-cong A₁≡A₂′
               (Id-cong (wkEq (step (step id)) (⊢→⊢∙ ⊢A₁′) A₁≡A₂)
                  (wkEqTerm (step (step id)) (⊢→⊢∙ ⊢A₁′) t₁≡t₂)
                  (refl (PE.subst (_⊢_∷_ _ _) wk2≡wk₂ $ var₀ ⊢A₁′))) $
             PE.subst (_⊢_≡_∷_ _ _ _)
               (PE.cong (Σ⟨_⟩_,_▷_▹_ s 𝟘 𝟘 (wk1 A₁)) $
                PE.cong₃ Id (lift-wk1 _ _) (lift-wk1 _ _) PE.refl) $
             refl (var₀ ⊢Singleton₁))
        )
        (⊢→⊢∙ ⊢Singleton₁)

    lemma₈′ :
      Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
      Γ ⊢ t ∷ A →
      Γ ∙ Singleton A t ⊢
        B U.[ consSubst
                (consSubst (wk1Subst idSubst)
                   (fst⟨ s ⟩ 𝟘 (wk1 A) (var x0)))
                (snd⟨ s ⟩ 𝟘 𝟘 (wk1 A) (Id (wk₂ A) (wk₂ t) (var x0))
                   (var x0))
            ]
    lemma₈′ ⊢B ⊢t =
      syntacticEq (lemma₈ (refl (syntacticTerm ⊢t)) (refl ⊢B) (refl ⊢t))
        .proj₁

    lemma₉ :
      Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
      Γ ⊢ v ∷ Id A t u →
      Γ ⊢
        B U.[ consSubst
                (consSubst (wk1Subst idSubst)
                   (fst⟨ s ⟩ 𝟘 (wk1 A) (var x0)))
                (snd⟨ s ⟩ 𝟘 𝟘 (wk1 A) (Id (wk₂ A) (wk₂ t) (var x0))
                   (var x0))
            ]
          [ prod s 𝟘 u v ]₀ ≡
        B [ u , v ]₁₀
    lemma₉ {A} {t} {B} {v} {u} ⊢B ⊢v =
      case inversion-Id (syntacticTerm ⊢v) of λ
        (_ , ⊢t , ⊢u) →
      case PE.subst (_⊢_∷_ _ _)
             (PE.sym $ PE.cong₃ Id
                (wk1-sgSubst _ _)
                (wk1-sgSubst _ _)
                PE.refl)
             ⊢v of λ
        ⊢v′ →

      B U.[ consSubst
              (consSubst (wk1Subst idSubst)
                 (fst⟨ s ⟩ 𝟘 (wk1 A) (var x0)))
              (snd⟨ s ⟩ 𝟘 𝟘 (wk1 A) (Id (wk₂ A) (wk₂ t) (var x0))
                 (var x0))
          ]
        [ prod s 𝟘 u v ]₀                                              ≡⟨ substCompEq B ⟩⊢≡

      B U.[ sgSubst (prod s 𝟘 u v) ₛ•ₛ
            consSubst
              (consSubst (wk1Subst idSubst)
                 (fst⟨ s ⟩ 𝟘 (wk1 A) (var x0)))
              (snd⟨ s ⟩ 𝟘 𝟘 (wk1 A) (Id (wk₂ A) (wk₂ t) (var x0))
                 (var x0))
          ]                                                            ≡⟨ (flip substVar-to-subst B λ where
                                                                             x0 → PE.refl
                                                                             (x0 +1) → PE.refl
                                                                             (_ +1 +1) → PE.refl) ⟩⊢≡
      B [ fst⟨ s ⟩ 𝟘 (wk1 A) (var x0) [ prod s 𝟘 u v ]₀
        , snd⟨ s ⟩ 𝟘 𝟘 (wk1 A) (Id (wk₂ A) (wk₂ t) (var x0)) (var x0)
            [ prod s 𝟘 u v ]₀
        ]₁₀                                                            ≡⟨ PE.cong₂ (λ t u → B [ t , u ]₁₀)
                                                                            (PE.trans fst⟨⟩-[] $
                                                                             PE.cong₂ (fst⟨ _ ⟩ _) (wk1-sgSubst _ _) PE.refl)
                                                                            (PE.trans snd⟨⟩-[] $
                                                                             PE.cong₃ (snd⟨ _ ⟩ _ _)
                                                                               (wk1-sgSubst _ _)
                                                                               (PE.cong₃ Id lemma₅ lemma₅ PE.refl)
                                                                               PE.refl) ⟩⊢≡
      B [ fst⟨ s ⟩ 𝟘 A (prod s 𝟘 u v)
        , snd⟨ s ⟩ 𝟘 𝟘 A (Id (wk1 A) (wk1 t) (var x0)) (prod s 𝟘 u v)
        ]₁₀                                                            ≡⟨ substTypeEq₂ (refl ⊢B)
                                                                            (fst⟨⟩-β-≡ (J-motive-context-type ⊢t) ⊢u ⊢v′ Σ-ok)
                                                                            (snd⟨⟩-β-≡ (J-motive-context-type ⊢t) ⊢u ⊢v′ Σ-ok) ⟩⊢∎
      B [ u , v ]₁₀                                                    ∎

  opaque
    unfolding Jᵉ

    -- An equality rule for Jᵉ.

    Jᵉ-cong :
      Γ ⊢ A₁ ≡ A₂ →
      Γ ⊢ t₁ ≡ t₂ ∷ A₁ →
      Γ ∙ A₁ ∙ Id (wk1 A₁) (wk1 t₁) (var x0) ⊢ B₁ ≡ B₂ →
      Γ ⊢ u₁ ≡ u₂ ∷ B₁ [ t₁ , rfl ]₁₀ →
      Γ ⊢ v₁ ≡ v₂ ∷ A₁ →
      Γ ⊢ w₁ ≡ w₂ ∷ Id A₁ t₁ v₁ →
      Γ ⊢ Jᵉ A₁ t₁ B₁ u₁ v₁ w₁ ≡ Jᵉ A₂ t₂ B₂ u₂ v₂ w₂ ∷ B₁ [ v₁ , w₁ ]₁₀
    Jᵉ-cong A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ w₁≡w₂ =
      case syntacticEq B₁≡B₂ of λ
        (⊢B₁  , _) →
      case syntacticEqTerm t₁≡t₂ of λ
        (⊢A₁ , ⊢t₁  , _) →
      case syntacticEqTerm w₁≡w₂ of λ
        (_ , ⊢w₁  , _) →
      conv
        (substᵉ-cong
           (ΠΣ-cong′ A₁≡A₂
              (Id-cong (wkEq₁ ⊢A₁ A₁≡A₂) (wkEqTerm₁ ⊢A₁ t₁≡t₂)
                 (refl (var₀ ⊢A₁)))
              Σ-ok)
           (lemma₈ A₁≡A₂ B₁≡B₂ t₁≡t₂)
           (prod-cong′ (J-motive-context-type ⊢t₁) t₁≡t₂
              (_⊢_≡_∷_.refl $
               PE.subst (_⊢_∷_ _ _)
                 (PE.sym $ PE.cong₃ Id
                    (wk1-sgSubst _ _)
                    (wk1-sgSubst _ _)
                    PE.refl) $
               rflⱼ ⊢t₁)
              Σ-ok)
           (prod-cong′ (J-motive-context-type ⊢t₁) v₁≡v₂
              (PE.subst (_⊢_≡_∷_ _ _ _)
                 (PE.sym $ PE.cong₃ Id
                    (wk1-sgSubst _ _)
                    (wk1-sgSubst _ _)
                    PE.refl)
                 w₁≡w₂)
              Σ-ok)
           (PE.subst (_⊢_≡_∷_ _ _ _)
              (PE.cong₃ Id wk₂-[,] wk₂-[,] PE.refl) $
            J-cong′ A₁≡A₂ t₁≡t₂ (lemma₆ A₁≡A₂ t₁≡t₂) (refl (lemma₇ ⊢t₁))
              v₁≡v₂ w₁≡w₂)
           (conv u₁≡u₂ $ sym $ lemma₉ ⊢B₁ (rflⱼ ⊢t₁)))
        (lemma₉ ⊢B₁ ⊢w₁)

  opaque

    -- A typing rule for Jᵉ.

    ⊢Jᵉ :
      Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
      Γ ⊢ u ∷ B [ t , rfl ]₁₀ →
      Γ ⊢ w ∷ Id A t v →
      Γ ⊢ Jᵉ A t B u v w ∷ B [ v , w ]₁₀
    ⊢Jᵉ ⊢B ⊢u ⊢w =
      case inversion-Id (syntacticTerm ⊢w) of λ
        (⊢A , ⊢t , ⊢v) →
      syntacticEqTerm
        (Jᵉ-cong (refl ⊢A) (refl ⊢t) (refl ⊢B) (refl ⊢u) (refl ⊢v)
           (refl ⊢w))
        .proj₂ .proj₁

  opaque
    unfolding Jᵉ

    -- A reduction rule for Jᵉ.

    Jᵉ-⇒*′ :
      Γ ⊢ t ≡ t′ ∷ A →
      Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
      Γ ⊢ u ∷ B [ t , rfl ]₁₀ →
      Γ ⊢ Jᵉ A t B u t′ rfl ⇒* u ∷ B [ t , rfl ]₁₀
    Jᵉ-⇒*′ {t} {t′} {A} {B} {u} t≡t′ ⊢B ⊢u =
      case syntacticEqTerm t≡t′ of λ
        (⊢A , ⊢t , _) →
      case PE.subst (_⊢_∷_ _ _)
             (PE.sym $ PE.cong₃ Id
                (wk1-sgSubst _ _)
                (wk1-sgSubst _ _)
                PE.refl) $
           rflⱼ ⊢t of λ
        ⊢rfl →
      case prod-cong′ (J-motive-context-type ⊢t) t≡t′ (refl ⊢rfl)
             Σ-ok of λ
        t,rfl≡t′,rfl →
      case ΠΣⱼ′ (Idⱼ (wkTerm₁ ⊢A ⊢t) (var₀ ⊢A)) Σ-ok of λ
        ⊢Singleton →

      substᵉ
        (Singleton A t)
        (B U.[ consSubst
                 (consSubst (wk1Subst idSubst)
                    (fst⟨ s ⟩ 𝟘 (wk1 A) (var x0)))
                 (snd⟨ s ⟩ 𝟘 𝟘 (wk1 A) (Id (wk₂ A) (wk₂ t) (var x0))
                    (var x0)) ])
        (prod s 𝟘 t rfl)
        (prod s 𝟘 t′ rfl)
        (J 𝟘 (𝟘 ∧ 𝟙) A t
           (Id (wk₂ (Singleton A t)) (wk₂ (prod s 𝟘 t rfl))
              (prod s 𝟘 (var x1) (var x0)))
           rfl t′ rfl)
        u                                                             ⇒⟨ _⊢_⇒_∷_.conv
                                                                           (substᵉ-subst (lemma₈′ ⊢B ⊢t)
                                                                              (conv
                                                                                 (PE.subst (_⊢_⇒_∷_ _ _ _)
                                                                                    (PE.cong₃ Id wk₂-[,] wk₂-[,] PE.refl) $
                                                                                  J-β-⇒ t≡t′ (lemma₆′ ⊢t) (lemma₇ ⊢t))
                                                                                  (Id-cong (refl ⊢Singleton)
                                                                                     (refl (⊢prod (J-motive-context-type ⊢t) ⊢t ⊢rfl Σ-ok))
                                                                                     t,rfl≡t′,rfl))
                                                                              (conv ⊢u $ sym $ lemma₉ ⊢B (rflⱼ ⊢t))) $
                                                                         _⊢_≡_.trans (lemma₉ ⊢B (rflⱼ′ t≡t′)) $
                                                                         substTypeEq₂ (refl ⊢B) (sym t≡t′) $
                                                                         PE.subst (_⊢_≡_∷_ _ _ _)
                                                                           (PE.sym $ PE.cong₃ Id
                                                                              (wk1-sgSubst _ _)
                                                                              (wk1-sgSubst _ _)
                                                                              PE.refl) $
                                                                         _⊢_≡_∷_.conv (refl (rflⱼ ⊢t)) $
                                                                         Id-cong (refl ⊢A) (refl ⊢t) t≡t′ ⟩
      substᵉ
        (Singleton A t)
        (B U.[ consSubst
                 (consSubst (wk1Subst idSubst)
                    (fst⟨ s ⟩ 𝟘 (wk1 A) (var x0)))
                 (snd⟨ s ⟩ 𝟘 𝟘 (wk1 A) (Id (wk₂ A) (wk₂ t) (var x0))
                    (var x0)) ])
        (prod s 𝟘 t rfl)
        (prod s 𝟘 t′ rfl)
        rfl
        u                                                             ⇒*⟨ conv*
                                                                            (substᵉ-⇒*′ (lemma₈′ ⊢B ⊢t) t,rfl≡t′,rfl
                                                                               (conv ⊢u $ sym $ lemma₉ ⊢B (rflⱼ ⊢t)))
                                                                            (lemma₉ ⊢B (rflⱼ ⊢t)) ⟩∎

      u                                                               ∎

  opaque

    -- Another reduction rule for Jᵉ.

    Jᵉ-⇒* :
      Γ ⊢ t ∷ A →
      Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
      Γ ⊢ u ∷ B [ t , rfl ]₁₀ →
      Γ ⊢ Jᵉ A t B u t rfl ⇒* u ∷ B [ t , rfl ]₁₀
    Jᵉ-⇒* ⊢t = Jᵉ-⇒*′ (refl ⊢t)

  opaque

    -- An equality rule for Jᵉ.

    Jᵉ-≡ :
      Γ ⊢ t ∷ A →
      Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
      Γ ⊢ u ∷ B [ t , rfl ]₁₀ →
      Γ ⊢ Jᵉ A t B u t rfl ≡ u ∷ B [ t , rfl ]₁₀
    Jᵉ-≡ ⊢t ⊢B ⊢u = subset*Term (Jᵉ-⇒* ⊢t ⊢B ⊢u)

  opaque
    unfolding Jᵉ substᵉ subst

    -- A certain reduction rule for Jᵉ is not valid.

    ¬-Jᵉ-subst :
      ¬ (∀ {n} {Γ : Con Term n} {A t : Term n} {B : Term (2+ n)}
           {u v w₁ w₂ : Term n} →
         Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
         Γ ⊢ u ∷ B [ t , rfl ]₁₀ →
         Γ ⊢ w₁ ⇒ w₂ ∷ Id A t v →
         Γ ⊢ Jᵉ A t B u v w₁ ⇒ Jᵉ A t B u v w₂ ∷ B [ v , w₁ ]₁₀)
    ¬-Jᵉ-subst Jᵉ-subst = ¬lhs⇒rhs lhs⇒rhs
      where
      Γ′                          : Con Term 0
      A′ t″ u′ v′ w₁′ w₂′ lhs rhs : Term 0
      B′                          : Term 2
      Γ′  = ε
      A′  = ℕ
      t″  = zero
      B′  = ℕ
      u′  = zero
      v′  = zero
      w₁′ = subst 𝟘 ℕ (Id ℕ zero zero) zero zero rfl rfl
      w₂′ = rfl
      lhs = Jᵉ A′ t″ B′ u′ v′ w₁′
      rhs = Jᵉ A′ t″ B′ u′ v′ w₂′

      ⊢B′ : Γ′ ∙ A′ ∙ Id (wk1 A′) (wk1 t″) (var x0) ⊢ B′
      ⊢B′ = ℕⱼ (⊢→⊢∙ (Idⱼ (zeroⱼ (⊢→⊢∙ (ℕⱼ ε))) (var₀ (ℕⱼ ε))))

      ⊢u′ : Γ′ ⊢ u′ ∷ B′ [ t″ , rfl ]₁₀
      ⊢u′ = zeroⱼ ε

      w₁′⇒w₂′ : Γ′ ⊢ w₁′ ⇒ w₂′ ∷ Id A′ t″ v′
      w₁′⇒w₂′ = subst-⇒
        (Idⱼ (zeroⱼ (⊢→⊢∙ (ℕⱼ ε))) (zeroⱼ (⊢→⊢∙ (ℕⱼ ε))))
        (zeroⱼ ε)
        (rflⱼ (zeroⱼ ε))

      lhs⇒rhs : Γ′ ⊢ lhs ⇒ rhs ∷ B′ [ v′ , w₁′ ]₁₀
      lhs⇒rhs = Jᵉ-subst ⊢B′ ⊢u′ w₁′⇒w₂′

      ¬lhs⇒rhs : ¬ Γ′ ⊢ lhs ⇒ rhs ∷ C
      ¬lhs⇒rhs (conv lhs⇒rhs _) = ¬lhs⇒rhs lhs⇒rhs
