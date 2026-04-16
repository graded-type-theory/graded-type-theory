------------------------------------------------------------------------
-- Admissible rules related to Erased
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality
open import Graded.Mode

module Definition.Typed.Consequences.Admissible.Erased
  {a b} {M : Set a} {Mode : Set b}
  {𝕄 : Modality M}
  (𝐌 : IsMode Mode 𝕄)
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Consequences.Admissible.Sigma R
open import Definition.Typed.Decidable.Internal 𝐌 R
import Definition.Typed.Decidable.Internal.Context 𝐌 R as IC
import Definition.Typed.Decidable.Internal.Substitution 𝐌 R as IS
import Definition.Typed.Decidable.Internal.Term 𝐌 R as I
import Definition.Typed.Decidable.Internal.Tests 𝐌 R as IT
import Definition.Typed.Decidable.Internal.Weakening 𝐌 R as IW
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Stability R
open import Definition.Typed.Substitution R
open import Definition.Typed.Weakening R
open import Definition.Typed.Well-formed R

open import Definition.Untyped M
import Definition.Untyped.Erased 𝕄 as Erased
open import Definition.Untyped.Identity 𝕄
open import Definition.Untyped.Sigma 𝕄

open import Tools.Bool
open import Tools.Fin
open import Tools.Function
import Tools.List as L
open import Tools.Maybe
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
import Tools.Vec as V

private variable
  m n                                             : Nat
  Γ                                               : Cons _ _
  A A₁ A₂ B B₁ B₂ t t₁ t₂ u u₁ u₂ v v₁ v₂ w w₁ w₂ : Term _
  l                                               : Lvl _
  s                                               : Strength

opaque
  unfolding Erased.Erased Erased.[_]

  -- A kind of inverse of []-cong′.

  []-cong′⁻¹ :
    let open Erased s in
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    Γ ⊢ [ t₁ ] ≡ [ t₂ ] ∷ Erased l A →
    Γ ⊢ t₁ ≡ t₂ ∷ A
  []-cong′⁻¹ [t₁]≡[t₂] =
    let _ , t₁≡t₂ , _ = prod-cong⁻¹ [t₁]≡[t₂] in
    t₁≡t₂

------------------------------------------------------------------------
-- Lemmas related to Jᵉ

-- It is assumed that []-cong is allowed.

module _ (ok : []-cong-allowed s) where

  open Erased s
  open Erased.Internal s 𝐌 R

  opaque
    unfolding Erased Jᵉ erased fst⟨_⟩ snd⟨_⟩ subst substᵉ [_]

    -- An equality rule for Jᵉ.

    Jᵉ-cong :
      {Γ : Cons m n} →
      Γ ⊢ A₁ ≡ A₂ →
      Γ ⊢ t₁ ≡ t₂ ∷ A₁ →
      Γ »∙ A₁ »∙ Id (wk1 A₁) (wk1 t₁) (var x0) ⊢ B₁ ≡ B₂ →
      Γ ⊢ u₁ ≡ u₂ ∷ B₁ [ t₁ , rfl ]₁₀ →
      Γ ⊢ v₁ ≡ v₂ ∷ A₁ →
      Γ ⊢ w₁ ≡ w₂ ∷ Id A₁ t₁ v₁ →
      Γ ⊢ Jᵉ A₁ t₁ B₁ u₁ v₁ w₁ ≡ Jᵉ A₂ t₂ B₂ u₂ v₂ w₂ ∷ B₁ [ v₁ , w₁ ]₁₀
    Jᵉ-cong
      {m} {n}
      {A₁} {A₂} {t₁} {t₂} {B₁} {B₂} {u₁} {u₂} {v₁} {v₂} {w₁} {w₂} {Γ}
      A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ w₁≡w₂ =
      case PE.singleton s of λ where
        (𝕤 , PE.refl) →
          check-and-equal-type-and-terms-sound γ Γᵢ lhs rhs goal 25
            PE.refl γ-wf (wf A₁≡A₂)
        (𝕨 , PE.refl) →
          check-and-equal-type-and-terms-sound γ Γᵢ lhs rhs goal 27
            PE.refl γ-wf (wf A₁≡A₂)
      where
      c : I.Constants
      c .I.gs                 = 0
      c .I.ss                 = 0
      c .I.bms                = 0
      c .I.ms                 = 12
      c .I.base-dcon-size     = m
      c .I.base-con-size      = n
      c .I.base-con-allowed   = true
      c .I.meta-con-size      = V.replicate 4 n V.++
                                V.replicate 2 (2+ n) V.++
                                V.replicate 6 n
      c .I.meta-con-term-kind = V.replicate 12 tm

      xA₁ xA₂ xt₁ xt₂ xu₁ xu₂ xv₁ xv₂ xw₁ xw₂ : I.Term c n
      xA₁ = I.varᵐ x0
      xA₂ = I.varᵐ x1
      xt₁ = I.varᵐ x2
      xt₂ = I.varᵐ x3
      xu₁ = I.varᵐ x6
      xu₂ = I.varᵐ x7
      xv₁ = I.varᵐ x8
      xv₂ = I.varᵐ x9
      xw₁ = I.varᵐ x10
      xw₂ = I.varᵐ x11

      xB₁ xB₂ : I.Term c (2+ n)
      xB₁ = I.varᵐ x4
      xB₂ = I.varᵐ x5

      Γᵢ : I.Cons c m n
      Γᵢ = I.base nothing I.» I.base

      lhs rhs goal : I.Term c n
      lhs  = Jᵉᵢ I.zeroᵘₗ xA₁ xt₁ xB₁ xu₁ xv₁ xw₁
      rhs  = Jᵉᵢ I.zeroᵘₗ xA₂ xt₂ xB₂ xu₂ xv₂ xw₂
      goal = I.subst xB₁ (I.cons (IS.sgSubst xv₁) xw₁)

      γ : I.Contexts c
      γ .I.grades       = V.ε
      γ .I.strengths    = V.ε
      γ .I.binder-modes = V.ε
      γ .I.⌜base⌝       = Γ
      γ .I.constraints⁰ = I.emptyᶜ⁰
      γ .I.constraints⁺ =
        I.box-cong-allowed sᵢ  L.∷
        I.unit-allowed sᵢ      L.∷
        I.σ-allowed sᵢ I.𝟘 I.𝟘 L.∷
        L.[]
      γ .I.metas .I.equalities =
        (_ , IT.meta xA₁ , IT.meta xA₂) L.∷
        (_ , IT.meta xt₁ , IT.meta xt₂) L.∷
        (_ , IT.meta xB₁ , IT.meta xB₂) L.∷
        (_ , IT.meta xu₁ , IT.meta xu₂) L.∷
        (_ , IT.meta xv₁ , IT.meta xv₂) L.∷
        (_ , IT.meta xw₁ , IT.meta xw₂) L.∷
        L.[]
      γ .I.metas .I.bindings = λ where
        (I.var! x0) → I.base , I.type A₁
        (I.var! x1) → I.base , I.type A₂
        (I.var! x2) → I.base , I.term t₁ xA₁
        (I.var! x3) → I.base , I.term t₂ xA₁
        (I.var! x4) →
          I.base I.∙ xA₁ I.∙
          I.Id (IW.wk[ 1 ] xA₁) (IW.wk[ 1 ] xt₁) (I.var x0) ,
          I.type B₁
        (I.var! x5) →
          I.base I.∙ xA₁ I.∙
          I.Id (IW.wk[ 1 ] xA₁) (IW.wk[ 1 ] xt₁) (I.var x0) ,
          I.type B₂
        (I.var! x6) →
          I.base ,
          I.term u₁
            (I.subst xB₁ (I.cons (IS.sgSubst xt₁) (I.rfl nothing)))
        (I.var! x7) →
          I.base ,
          I.term u₂
            (I.subst xB₁ (I.cons (IS.sgSubst xt₁) (I.rfl nothing)))
        (I.var! x8)         → I.base , I.term v₁ xA₁
        (I.var! x9)         → I.base , I.term v₂ xA₁
        (I.var! x10)        → I.base , I.term w₁ (I.Id xA₁ xt₁ xv₁)
        (I.var! x11)        → I.base , I.term w₂ (I.Id xA₁ xt₁ xv₁)
        (I.var not-x12 _ _)

      opaque

        γ-wf : IC.Contexts-wf (I.base nothing) γ
        γ-wf =
          let ⊢A₁ , ⊢A₂      = wf-⊢ A₁≡A₂
              _ , ⊢t₁ , ⊢t₂  = wf-⊢ t₁≡t₂
              ⊢B₁ , ⊢B₂      = wf-⊢ B₁≡B₂
              _ , ⊢u₁ , ⊢u₂  = wf-⊢ u₁≡u₂
              _ , ⊢v₁ , ⊢v₂  = wf-⊢ v₁≡v₂
              _ , ⊢w₁ , ⊢w₂  = wf-⊢ w₁≡w₂
              ⊢Γ             = wf-⊢ ⊢A₁
              Unit-ok , Σ-ok = []-cong→Erased ok
          in
          λ where
            .IC.constraints-wf →
              case PE.singleton s of λ where
                (𝕤 , PE.refl) → ok L.∷ Unit-ok L.∷ Σ-ok L.∷ L.[]
                (𝕨 , PE.refl) → ok L.∷ Unit-ok L.∷ Σ-ok L.∷ L.[]
            .IC.metas-wf .IC.equalities-wf →
               (reflConEq ⊢Γ , IC.type A₁≡A₂) L.∷
               (reflConEq ⊢Γ , IC.term (refl ⊢A₁) t₁≡t₂) L.∷
               (reflConEq (∙ Idⱼ′ (wk₁ ⊢A₁ ⊢t₁) (var₀ ⊢A₁)) ,
                IC.type B₁≡B₂) L.∷
               (reflConEq ⊢Γ ,
                IC.term (J-motive-rfl-cong (refl ⊢B₁) (refl ⊢t₁))
                  u₁≡u₂) L.∷
               (reflConEq ⊢Γ , IC.term (refl ⊢A₁) v₁≡v₂) L.∷
               (reflConEq ⊢Γ , IC.term (refl (Idⱼ′ ⊢t₁ ⊢v₁)) w₁≡w₂) L.∷
               L.[]
            .IC.metas-wf .IC.bindings-wf → λ where
              (I.var! x0)          → ⊢A₁
              (I.var! x1)          → ⊢A₂
              (I.var! x2)          → ⊢t₁
              (I.var! x3)          → ⊢t₂
              (I.var! x4)          → ⊢B₁
              (I.var! x5)          → ⊢B₂
              (I.var! x6)          → ⊢u₁
              (I.var! x7)          → ⊢u₂
              (I.var! x8)          → ⊢v₁
              (I.var! x9)          → ⊢v₂
              (I.var! x10)         → ⊢w₁
              (I.var! x11)         → ⊢w₂
              (I.var  not-x12 _ _)

  opaque

    -- A typing rule for Jᵉ.

    ⊢Jᵉ :
      Γ »∙ A »∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
      Γ ⊢ u ∷ B [ t , rfl ]₁₀ →
      Γ ⊢ w ∷ Id A t v →
      Γ ⊢ Jᵉ A t B u v w ∷ B [ v , w ]₁₀
    ⊢Jᵉ ⊢B ⊢u ⊢w =
      let ⊢A , ⊢t , ⊢v = inversion-Id (wf-⊢ ⊢w) in
      wf-⊢
        (Jᵉ-cong (refl ⊢A) (refl ⊢t) (refl ⊢B) (refl ⊢u) (refl ⊢v)
           (refl ⊢w))
        .proj₂ .proj₁

  opaque
    unfolding Erased Jᵉ erased fst⟨_⟩ snd⟨_⟩ subst substᵉ [_]

    -- An equality rule for Jᵉ.

    Jᵉ-≡ :
      {Γ : Cons m n} →
      Γ ⊢ t ∷ A →
      Γ »∙ A »∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
      Γ ⊢ u ∷ B [ t , rfl ]₁₀ →
      Γ ⊢ Jᵉ A t B u t rfl ≡ u ∷ B [ t , rfl ]₁₀
    Jᵉ-≡ {m} {n} {t} {A} {B} {u} {Γ} ⊢t ⊢B ⊢u =
      case PE.singleton s of λ where
        (𝕤 , PE.refl) →
          check-and-equal-type-and-terms-sound γ Γᵢ lhs rhs goal 25
            PE.refl γ-wf (wf ⊢t)
        (𝕨 , PE.refl) →
          check-and-equal-type-and-terms-sound γ Γᵢ lhs rhs goal 27
            PE.refl γ-wf (wf ⊢t)
      where
      c : I.Constants
      c .I.gs                 = 0
      c .I.ss                 = 0
      c .I.bms                = 0
      c .I.ms                 = 4
      c .I.base-dcon-size     = m
      c .I.base-con-size      = n
      c .I.base-con-allowed   = true
      c .I.meta-con-size      = V.replicate 2 n V.++ 2+ n V.∷ n V.∷ V.ε
      c .I.meta-con-term-kind = V.replicate 4 tm

      xA xt xu : I.Term c n
      xA = I.varᵐ x0
      xt = I.varᵐ x1
      xu = I.varᵐ x3

      xB : I.Term c (2+ n)
      xB = I.varᵐ x2

      Γᵢ : I.Cons c m n
      Γᵢ = I.base nothing I.» I.base

      lhs rhs goal : I.Term c n
      lhs  = Jᵉᵢ I.zeroᵘₗ xA xt xB xu xt (I.rfl nothing)
      rhs  = xu
      goal = I.subst xB (I.cons (IS.sgSubst xt) (I.rfl nothing))

      γ : I.Contexts c
      γ .I.grades       = V.ε
      γ .I.strengths    = V.ε
      γ .I.binder-modes = V.ε
      γ .I.⌜base⌝       = Γ
      γ .I.constraints⁰ = I.emptyᶜ⁰
      γ .I.constraints⁺ =
        I.box-cong-allowed sᵢ  L.∷
        I.unit-allowed sᵢ      L.∷
        I.σ-allowed sᵢ I.𝟘 I.𝟘 L.∷
        L.[]
      γ .I.metas .I.equalities = L.[]
      γ .I.metas .I.bindings   = λ where
        (I.var! x0) → I.base , I.type A
        (I.var! x1) → I.base , I.term t xA
        (I.var! x2) →
          I.base I.∙ xA I.∙
          I.Id (IW.wk[ 1 ] xA) (IW.wk[ 1 ] xt) (I.var x0) ,
          I.type B
        (I.var! x3) →
          I.base ,
          I.term u (I.subst xB (I.cons (IS.sgSubst xt) (I.rfl nothing)))
        (I.var not-x4 _ _)

      opaque

        γ-wf : IC.Contexts-wf (I.base nothing) γ
        γ-wf =
          let Unit-ok , Σ-ok = []-cong→Erased ok in
          λ where
            .IC.constraints-wf →
              case PE.singleton s of λ where
                (𝕤 , PE.refl) → ok L.∷ Unit-ok L.∷ Σ-ok L.∷ L.[]
                (𝕨 , PE.refl) → ok L.∷ Unit-ok L.∷ Σ-ok L.∷ L.[]
            .IC.metas-wf .IC.equalities-wf → L.[]
            .IC.metas-wf .IC.bindings-wf → λ where
              (I.var! x0)         → wf-⊢ ⊢t
              (I.var! x1)         → ⊢t
              (I.var! x2)         → ⊢B
              (I.var! x3)         → ⊢u
              (I.var  not-x4 _ _)
