------------------------------------------------------------------------
-- Typing and equality rules related to Sum
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality
open import Graded.Mode

module Definition.Typed.Consequences.Admissible.Sum
  {ℓ₁ ℓ₂} {M : Set ℓ₁} {Mode : Set ℓ₂}
  {𝕄 : Modality M}
  (open Modality 𝕄)
  (𝐌 : IsMode Mode 𝕄)
  (R : Type-restrictions 𝕄)
  (open Type-restrictions R)
  -- It is assumed that certain Π- and Σ-types are allowed.
  (Σ-ok₁ : Σʷ-allowed 𝟙 𝟙)
  (Σ-ok₂ : Σʷ-allowed 𝟙 (𝟙 ∧ 𝟘))
  (Π-ok : Π-allowed 𝟙 𝟘)
  -- It is assumed that both unit types are allowed.
  (Unit-ok : ∀ {s} → Unit-allowed s)
  where

open import Definition.Typed R
open import Definition.Typed.Decidable.Internal 𝐌 R
import Definition.Typed.Decidable.Internal.Context 𝐌 R as IC
import Definition.Typed.Decidable.Internal.Term 𝐌 R as I
import Definition.Typed.Decidable.Internal.Tests 𝐌 R as IT
import Definition.Typed.Decidable.Internal.Substitution 𝐌 R as IS
import Definition.Typed.Decidable.Internal.Weakening 𝐌 R as IW
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Stability R
open import Definition.Typed.Syntactic R
open import Definition.Typed.Well-formed R

open import Definition.Untyped M
open import Definition.Untyped.Sum R
open Internal 𝐌
open import Definition.Untyped.Bool.Greatest-lower-bound 𝕄
open import Definition.Untyped.Empty 𝕄
open import Definition.Untyped.Nat 𝕄
open import Definition.Untyped.Sup R

import Tools.Bool as B
open import Tools.Fin
open import Tools.Maybe
open import Tools.Nat hiding (_+_)
open import Tools.Product
import Tools.PropositionalEquality as PE
import Tools.List as L
import Tools.Vec as V

private variable
  m n ms k : Nat
  a a₁ a₂ b b₁ b₂ A A₁ A₂ B B₁ B₂ : Term _
  t t₁ t₂ P P₁ P₂ l l₁ l₂ r r₁ r₂ : Term _
  Γ : Cons _ _
  q p : M


------------------------------------------------------------------------
-- Typing rules for Sum′, Sum, inl and inr

private
  module Defs
    (Γ : Cons m n) (meta-con-size : V.Vec Nat ms)
    where
    c : I.Constants
    c .I.gs = 0
    c .I.ss = 0
    c .I.bms = 0
    c .I.ms = ms
    c .I.meta-con-size = meta-con-size
    c .I.base-dcon-size = m
    c .I.base-con-allowed = B.true
    c .I.base-con-size = n

    γ :
      (∀ {n} (x : I.Meta-var c n) → I.Con c n × I.Type-or-term c n) →
      I.Contexts c
    γ _ .I.grades = V.ε
    γ _ .I.strengths = V.ε
    γ _ .I.binder-modes = V.ε
    γ M .I.metas .I.bindings = M
    γ _ .I.metas .I.equalities = L.[]
    γ _ .I.⌜base⌝ = Γ
    γ _ .I.constraints⁰ = I.emptyᶜ⁰
    γ _ .I.constraints⁺ =
      I.unit-allowed I.𝕤             L.∷
      I.unit-allowed I.𝕨             L.∷
      I.π-allowed I.𝟙 I.𝟘            L.∷
      I.σʷ-allowed I.𝟙 I.𝟙           L.∷
      I.σʷ-allowed I.𝟙 (I.𝟙 I.∧ I.𝟘) L.∷
      L.[]

    γ′ :
      I.Meta-con c →
      I.Contexts c
    γ′ M = record (γ (M .I.bindings)) { metas = M }

opaque
  unfolding Sum Sum′ boolrec natcase emptyrec-sink true false OK Target Bool

  -- Congruence for Sum

  Sum-cong :
    Γ ⊢ a₁ ≡ a₂ ∷Level →
    Γ ⊢ b₁ ≡ b₂ ∷Level →
    Γ ⊢ A₁ ≡ A₂ ∷ U a₁ →
    Γ ⊢ B₁ ≡ B₂ ∷ U b₁ →
    Γ ⊢ Sum a₁ b₁ A₁ B₁ ≡ Sum a₂ b₂ A₂ B₂ ∷ U (a₁ supᵘₗ b₁)
  Sum-cong {(m)} {(n)} {Γ} {a₁} {a₂} {b₁} {b₂} {A₁} {A₂} {B₁} {B₂}
    a₁≡a₂ b₁≡b₂ A₁≡A₂ B₁≡B₂ =
    let ⊢a₁ , ⊢a₂ = wf-⊢≡∷L a₁≡a₂
        ⊢b₁ , ⊢b₂ = wf-⊢≡∷L b₁≡b₂
        _ , ⊢A₁ , ⊢A₂ = wf-⊢≡∷ A₁≡A₂
        _ , ⊢B₁ , ⊢B₂ = wf-⊢≡∷ B₁≡B₂
        ⊢Γ = wfTerm ⊢A₁
    in  check-and-equal-type-and-terms-sound
      (γ′ λ where
        .I.equalities →
          (_ , IT.meta xa₁ , IT.meta xa₂) L.∷
          (_ , IT.meta xb₁ , IT.meta xb₂) L.∷
          (_ , IT.meta xA₁ , IT.meta xA₂) L.∷
          (_ , IT.meta xB₁ , IT.meta xB₂) L.∷
          L.[]
        .I.bindings → λ where
          (I.var! x0) → I.base , I.level a₁
          (I.var! x1) → I.base , I.level a₂
          (I.var! x2) → I.base , I.level b₁
          (I.var! x3) → I.base , I.level b₂
          (I.var! x4) → I.base , I.term A₁ (I.U xa₁)
          (I.var! x5) → I.base , I.term A₂ (I.U xa₂)
          (I.var! x6) → I.base , I.term B₁ (I.U xb₁)
          (I.var! x7) → I.base , I.term B₂ (I.U xb₂)
          (I.var not-x8 _))
      (I.base nothing I.» I.base)
      (Sumᵢ xa₁ xb₁ xA₁ xB₁)
      (Sumᵢ xa₂ xb₂ xA₂ xB₂)
      (I.U (xa₁ I.supᵘₗ xb₁))
      30
      PE.refl
      (λ where
          .IC.constraints-wf →
            Unit-ok L.∷
            Unit-ok L.∷
            Π-ok L.∷
            Σ-ok₁ L.∷
            Σ-ok₂ L.∷
            L.[]
          .IC.metas-wf .IC.bindings-wf → λ where
            (I.var! x0) → ⊢a₁
            (I.var! x1) → ⊢a₂
            (I.var! x2) → ⊢b₁
            (I.var! x3) → ⊢b₂
            (I.var! x4) → ⊢A₁
            (I.var! x5) → conv ⊢A₂ (U-cong-⊢≡ a₁≡a₂)
            (I.var! x6) → ⊢B₁
            (I.var! x7) → conv ⊢B₂ (U-cong-⊢≡ b₁≡b₂)
            (I.var  not-x8 _)
          .IC.metas-wf .IC.equalities-wf →
            (reflConEq ⊢Γ , IC.level a₁≡a₂) L.∷
            (reflConEq ⊢Γ , IC.level b₁≡b₂) L.∷
            (reflConEq ⊢Γ , IC.term (U-cong-⊢≡ a₁≡a₂) A₁≡A₂) L.∷
            (reflConEq ⊢Γ , IC.term (U-cong-⊢≡ b₁≡b₂) B₁≡B₂) L.∷
            L.[])
      ⊢Γ
    where
    open Defs Γ
      (V.replicate 8 n)

    xa₁ xa₂ xb₁ xb₂ xA₁ xA₂ xB₁ xB₂ : I.Term c n
    xa₁ = I.varᵐ x0
    xa₂ = I.varᵐ x1
    xb₁ = I.varᵐ x2
    xb₂ = I.varᵐ x3
    xA₁ = I.varᵐ x4
    xA₂ = I.varᵐ x5
    xB₁ = I.varᵐ x6
    xB₂ = I.varᵐ x7

opaque

  -- A typing rule for Sum.

  ⊢Sum∷U :
    Γ ⊢ a ∷Level →
    Γ ⊢ b ∷Level →
    Γ ⊢ A ∷ U a →
    Γ ⊢ B ∷ U b →
    Γ ⊢ Sum a b A B ∷ U (a supᵘₗ b)
  ⊢Sum∷U ⊢a ⊢b ⊢A ⊢B =
    syntacticEqTerm
      (Sum-cong (refl-⊢≡∷L ⊢a) (refl-⊢≡∷L ⊢b) (refl ⊢A) (refl ⊢B))
      .proj₂ .proj₁

opaque

  -- A typing rule for Sum.

  ⊢Sum :
    Γ ⊢ a ∷Level →
    Γ ⊢ b ∷Level →
    Γ ⊢ A ∷ U a →
    Γ ⊢ B ∷ U b →
    Γ ⊢ Sum a b A B
  ⊢Sum ⊢a ⊢b ⊢A ⊢B =
    univ (⊢Sum∷U ⊢a ⊢b ⊢A ⊢B)

opaque
  unfolding inl Sum Sum′ boolrec natcase emptyrec-sink true false OK Target Bool

  -- Congruence for inl

  inl-cong :
    Γ ⊢ A ∷ U a →
    Γ ⊢ B ∷ U b →
    Γ ⊢ t₁ ≡ t₂ ∷ A →
    Γ ⊢ inl t₁ ≡ inl t₂ ∷ Sum a b A B
  inl-cong {(m)} {(n)} {Γ} {A} {a} {B} {b} {t₁} {t₂} ⊢A ⊢B t₁≡t₂ =
    let ⊢a = inversion-U-Level (syntacticTerm ⊢A)
        ⊢b = inversion-U-Level (syntacticTerm ⊢B)
        _ , ⊢t₁ , ⊢t₂ = wf-⊢≡∷ t₁≡t₂
        ⊢Γ = wfTerm ⊢A
    in
    check-and-equal-type-and-terms-sound
      (γ′ λ where
        .I.equalities →
          (_ , IT.meta xt₁ , IT.meta xt₂) L.∷ L.[]
        .I.bindings → λ where
          (I.var! x0) → I.base , I.level a
          (I.var! x1) → I.base , I.level b
          (I.var! x2) → I.base , I.term A (I.U xa)
          (I.var! x3) → I.base , I.term B (I.U xb)
          (I.var! x4) → I.base , I.term t₁ xA
          (I.var! x5) → I.base , I.term t₂ xA
          (I.var not-x6 _))
      (I.base nothing I.» I.base)
      (inlᵢ xa xb xA xB xt₁)
      (inlᵢ xa xb xA xB xt₂)
      (Sumᵢ xa xb xA xB)
      35
      PE.refl
      (λ where
          .IC.constraints-wf →
            Unit-ok L.∷
            Unit-ok L.∷
            Π-ok L.∷
            Σ-ok₁ L.∷
            Σ-ok₂ L.∷
            L.[]
          .IC.metas-wf .IC.bindings-wf → λ where
            (I.var! x0) → ⊢a
            (I.var! x1) → ⊢b
            (I.var! x2) → ⊢A
            (I.var! x3) → ⊢B
            (I.var! x4) → ⊢t₁
            (I.var! x5) → ⊢t₂
            (I.var  not-x6 _)
          .IC.metas-wf .IC.equalities-wf →
            (reflConEq ⊢Γ , IC.term (refl (univ ⊢A)) t₁≡t₂) L.∷ L.[])
      ⊢Γ
    where
    open Defs Γ
      (V.replicate 6 n)

    xa xb xA xB xt₁ xt₂ : I.Term c n
    xa = I.varᵐ x0
    xb = I.varᵐ x1
    xA = I.varᵐ x2
    xB = I.varᵐ x3
    xt₁ = I.varᵐ x4
    xt₂ = I.varᵐ x5

opaque

  -- A typing rule for inl

  ⊢inl :
    Γ ⊢ A ∷ U a →
    Γ ⊢ B ∷ U b →
    Γ ⊢ t ∷ A →
    Γ ⊢ inl t ∷ Sum a b A B
  ⊢inl ⊢A ⊢B ⊢t =
    syntacticEqTerm
      (inl-cong ⊢A ⊢B (refl ⊢t))
      .proj₂ .proj₁

opaque
  unfolding inr Sum Sum′ boolrec natcase emptyrec-sink true false OK Target Bool

  -- Congruence for inr

  inr-cong :
    Γ ⊢ A ∷ U a →
    Γ ⊢ B ∷ U b →
    Γ ⊢ t₁ ≡ t₂ ∷ B →
    Γ ⊢ inr t₁ ≡ inr t₂ ∷ Sum a b A B
  inr-cong {(m)} {(n)} {Γ} {A} {a} {B} {b} {t₁} {t₂} ⊢A ⊢B t₁≡t₂ =
    let ⊢a = inversion-U-Level (syntacticTerm ⊢A)
        ⊢b = inversion-U-Level (syntacticTerm ⊢B)
        _ , ⊢t₁ , ⊢t₂ = wf-⊢≡∷ t₁≡t₂
        ⊢Γ = wfTerm ⊢A
    in
    check-and-equal-type-and-terms-sound
      (γ′ λ where
        .I.equalities →
          (_ , IT.meta xt₁ , IT.meta xt₂) L.∷ L.[]
        .I.bindings → λ where
          (I.var! x0) → I.base , I.level a
          (I.var! x1) → I.base , I.level b
          (I.var! x2) → I.base , I.term A (I.U xa)
          (I.var! x3) → I.base , I.term B (I.U xb)
          (I.var! x4) → I.base , I.term t₁ xB
          (I.var! x5) → I.base , I.term t₂ xB
          (I.var not-x6 _))
      (I.base nothing I.» I.base)
      (inrᵢ xa xb xA xB xt₁)
      (inrᵢ xa xb xA xB xt₂)
      (Sumᵢ xa xb xA xB)
      35
      PE.refl
      (λ where
          .IC.constraints-wf →
            Unit-ok L.∷
            Unit-ok L.∷
            Π-ok L.∷
            Σ-ok₁ L.∷
            Σ-ok₂ L.∷
            L.[]
          .IC.metas-wf .IC.bindings-wf → λ where
            (I.var! x0) → ⊢a
            (I.var! x1) → ⊢b
            (I.var! x2) → ⊢A
            (I.var! x3) → ⊢B
            (I.var! x4) → ⊢t₁
            (I.var! x5) → ⊢t₂
            (I.var  not-x6 _)
          .IC.metas-wf .IC.equalities-wf →
            (reflConEq ⊢Γ , IC.term (refl (univ ⊢B)) t₁≡t₂) L.∷ L.[])
      ⊢Γ
    where
    open Defs Γ
      (V.replicate 6 n)

    xa xb xA xB xt₁ xt₂ : I.Term c n
    xa = I.varᵐ x0
    xb = I.varᵐ x1
    xA = I.varᵐ x2
    xB = I.varᵐ x3
    xt₁ = I.varᵐ x4
    xt₂ = I.varᵐ x5

opaque

  -- A typing rule for inr

  ⊢inr :
    Γ ⊢ A ∷ U a →
    Γ ⊢ B ∷ U b →
    Γ ⊢ t ∷ B →
    Γ ⊢ inr t ∷ Sum a b A B
  ⊢inr ⊢A ⊢B ⊢t =
    syntacticEqTerm
      (inr-cong ⊢A ⊢B (refl ⊢t))
      .proj₂ .proj₁

private
  module Defs′
    (q p : M)
    (Γ : Cons m n) (meta-con-size : V.Vec Nat ms)
    where
    c : I.Constants
    c .I.gs = 2
    c .I.ss = 0
    c .I.bms = 0
    c .I.ms = ms
    c .I.meta-con-size = meta-con-size
    c .I.base-dcon-size = m
    c .I.base-con-allowed = B.true
    c .I.base-con-size = n

    xq xp : I.Termᵍ 2
    xq = I.var x0
    xp = I.var x1

    sumrecᵢ′ :
      (a b A B : I.Term c k) →
      (P l r : I.Term c (1+ k)) →
      I.Term c k → I.Term c k
    sumrecᵢ′ = sumrecᵢ xq xp

    γ :
      (∀ {n} (x : I.Meta-var c n) → I.Con c n × I.Type-or-term c n) →
      I.Contexts c
    γ _ .I.grades = q V.∷ p V.∷ V.ε
    γ _ .I.strengths = V.ε
    γ _ .I.binder-modes = V.ε
    γ M .I.metas .I.bindings = M
    γ _ .I.metas .I.equalities = L.[]
    γ _ .I.⌜base⌝ = Γ
    γ _ .I.constraints⁰ = I.emptyᶜ⁰
    γ _ .I.constraints⁺ =
      I.unit-allowed I.𝕤                     L.∷
      I.unit-allowed I.𝕨                     L.∷
      I.π-allowed I.𝟙 I.𝟘                    L.∷
      I.π-allowed I.𝟙 (xq I.+ xp)            L.∷
      I.π-allowed xp xq                      L.∷
      I.σʷ-allowed I.𝟙 I.𝟙                   L.∷
      I.σʷ-allowed I.𝟙 (I.𝟙 I.∧ I.𝟘)         L.∷
      L.[]

    γ′ :
      I.Meta-con c →
      I.Contexts c
    γ′ M = record (γ (M .I.bindings)) { metas = M }

opaque
  unfolding sumrec Bool OK Target boolrec emptyrec-sink false natcase true Sum Sum′ inl inr Targetˢʳ

  -- Congruence for sumrec

  ⊢sumrec :
    Γ ⊢ a ∷Level →
    Γ ⊢ b ∷Level →
    Γ ⊢ A ∷ U a →
    Γ ⊢ B ∷ U b →
    Γ »∙ Sum a b A B ⊢ P →
    Γ »∙ A ⊢ l ∷ P [ inl (var x0) ]↑ →
    Γ »∙ B ⊢ r ∷ P [ inr (var x0) ]↑ →
    Γ ⊢ t ∷ Sum a b A B →
    Π-allowed p q →
    Π-allowed 𝟙 (q + p) →
    Γ ⊢ sumrec q p a b A B P l r t ∷ P [ t ]₀
  ⊢sumrec {(m)} {(n)} {Γ} {a} {b} {A} {B} {P}
    {l} {r} {t} {p} {q}
    ⊢a ⊢b ⊢A ⊢B ⊢P ⊢l ⊢r ⊢t Π-ok₁ Π-ok₂ =
      let ⊢Γ = wfTerm ⊢t
          Sumᵢ′ = Sumᵢ xa xb xA xB
      in  check-type-and-term-sound
        (γ′ λ where
          .I.equalities → L.[]
          .I.bindings → λ where
            (I.var! x0) → I.base , I.level a
            (I.var! x1) → I.base , I.level b
            (I.var! x2) → I.base , I.term A (I.U xa)
            (I.var! x3) → I.base , I.term B (I.U xb)
            (I.var! x4) → I.base I.∙ Sumᵢ′ , I.type P
            (I.var! x5) →
              I.base I.∙ xA , I.term l (I.subst xP (I.cons (IS.wkSubst 1 I.id)
                (inlᵢ (IW.wk (step id) xa) (IW.wk (step id) xb)
                  (IW.wk (step id) xA) (IW.wk (step id) xB) (I.var x0))))
            (I.var! x6) →
              I.base I.∙ xB , I.term r (I.subst xP (I.cons (IS.wkSubst 1 I.id)
                (inrᵢ (IW.wk (step id) xa) (IW.wk (step id) xb)
                  (IW.wk (step id) xA) (IW.wk (step id) xB) (I.var x0))))
            (I.var! x7) → I.base , I.term t Sumᵢ′
            (I.var not-x8 _))
        (I.base nothing I.» I.base)
        (sumrecᵢ′ xa xb xA xB xP xl xr xt)
        (I.subst xP (IS.sgSubst xt))
        48
        PE.refl
        (λ where
          .IC.constraints-wf →
            Unit-ok L.∷ Unit-ok L.∷
            Π-ok L.∷ Π-ok₂ L.∷ Π-ok₁ L.∷
            Σ-ok₁ L.∷ Σ-ok₂ L.∷ L.[]
          .IC.metas-wf .IC.equalities-wf → L.[]
          .IC.metas-wf .IC.bindings-wf → λ where
            (I.var! x0) → ⊢a
            (I.var! x1) → ⊢b
            (I.var! x2) → ⊢A
            (I.var! x3) → ⊢B
            (I.var! x4) → ⊢P
            (I.var! x5) → ⊢l
            (I.var! x6) → ⊢r
            (I.var! x7) → ⊢t
            (I.var  not-x8 _))
        ⊢Γ
    where
    open Defs′ q p Γ
      (n V.∷ n V.∷ n V.∷ n V.∷ (1+ n) V.∷
      (1+ n) V.∷ (1+ n) V.∷ n V.∷ V.ε)

    xa xb xA xB xt : I.Term c n
    xa = I.varᵐ x0
    xb = I.varᵐ x1
    xA = I.varᵐ x2
    xB = I.varᵐ x3
    xt = I.varᵐ x7

    xP xl xr : I.Term c (1+ n)
    xP = I.varᵐ x4
    xl = I.varᵐ x5
    xr = I.varᵐ x6

opaque
  unfolding sumrec Bool OK Target boolrec emptyrec-sink false natcase true Sum Sum′ inl inr Targetˢʳ

  -- An equality rule for sumrec

  ⊢sumrec-inl≡ :
    Γ ⊢ a ∷Level →
    Γ ⊢ b ∷Level →
    Γ ⊢ A ∷ U a →
    Γ ⊢ B ∷ U b →
    Γ »∙ Sum a b A B ⊢ P →
    Γ »∙ A ⊢ l ∷ P [ inl (var x0) ]↑ →
    Γ »∙ B ⊢ r ∷ P [ inr (var x0) ]↑ →
    Γ ⊢ t ∷ A →
    Π-allowed p q →
    Π-allowed 𝟙 (q + p) →
    Γ ⊢ sumrec q p a b A B P l r (inl t) ≡ l [ t ]₀ ∷ P [ inl t ]₀
  ⊢sumrec-inl≡
    {(m)} {(n)} {Γ} {a} {b} {A} {B} {P}
    {l} {r} {t} {p} {q}
    ⊢a ⊢b ⊢A ⊢B ⊢P ⊢l ⊢r ⊢t Π-ok₁ Π-ok₂ =
      let ⊢Γ = wfTerm ⊢t
          Sumᵢ′ = Sumᵢ xa xb xA xB
      in  check-and-equal-type-and-terms-sound
        (γ′ λ where
          .I.equalities → L.[]
          .I.bindings → λ where
            (I.var! x0) → I.base , I.level a
            (I.var! x1) → I.base , I.level b
            (I.var! x2) → I.base , I.term A (I.U xa)
            (I.var! x3) → I.base , I.term B (I.U xb)
            (I.var! x4) → I.base I.∙ Sumᵢ′ , I.type P
            (I.var! x5) → I.base I.∙ xA , I.term l (I.subst xP (I.cons (IS.wkSubst 1 I.id)
              (inlᵢ (IW.wk (step id) xa) (IW.wk (step id) xb) (IW.wk (step id) xA) (IW.wk (step id) xB) (I.var x0))))
            (I.var! x6) → I.base I.∙ xB , I.term r (I.subst xP (I.cons (IS.wkSubst 1 I.id)
              (inrᵢ (IW.wk (step id) xa) (IW.wk (step id) xb) (IW.wk (step id) xA) (IW.wk (step id) xB) (I.var x0))))
            (I.var! x7) → I.base , I.term t xA
            (I.var not-x8 _))
         (I.base nothing I.» I.base)
         (sumrecᵢ′ xa xb xA xB xP xl xr (inlᵢ xa xb xA xB xt))
         (I.subst xl (IS.sgSubst xt))
         (I.subst xP (IS.sgSubst (inlᵢ xa xb xA xB xt)))
         50
         PE.refl
         (λ where
           .IC.constraints-wf →
             Unit-ok L.∷ Unit-ok L.∷
             Π-ok L.∷ Π-ok₂ L.∷ Π-ok₁ L.∷
             Σ-ok₁ L.∷ Σ-ok₂ L.∷ L.[]
           .IC.metas-wf .IC.equalities-wf → L.[]
           .IC.metas-wf .IC.bindings-wf → λ where
             (I.var! x0) → ⊢a
             (I.var! x1) → ⊢b
             (I.var! x2) → ⊢A
             (I.var! x3) → ⊢B
             (I.var! x4) → ⊢P
             (I.var! x5) → ⊢l
             (I.var! x6) → ⊢r
             (I.var! x7) → ⊢t
             (I.var not-x8 _))
         ⊢Γ

    where
    open Defs′ q p Γ
      (n V.∷ n V.∷ n V.∷ n V.∷ (1+ n) V.∷
      (1+ n) V.∷ (1+ n) V.∷ n V.∷ V.ε)

    xa xb xA xB xt : I.Term c n
    xa = I.varᵐ x0
    xb = I.varᵐ x1
    xA = I.varᵐ x2
    xB = I.varᵐ x3
    xt = I.varᵐ x7

    xP xl xr : I.Term c (1+ n)
    xP = I.varᵐ x4
    xl = I.varᵐ x5
    xr = I.varᵐ x6

opaque
  unfolding sumrec Bool OK Target boolrec emptyrec-sink false natcase true Sum Sum′ inl inr Targetˢʳ

  -- An equality rule for sumrec

  ⊢sumrec-inr≡ :
    Γ ⊢ a ∷Level →
    Γ ⊢ b ∷Level →
    Γ ⊢ A ∷ U a →
    Γ ⊢ B ∷ U b →
    Γ »∙ Sum a b A B ⊢ P →
    Γ »∙ A ⊢ l ∷ P [ inl (var x0) ]↑ →
    Γ »∙ B ⊢ r ∷ P [ inr (var x0) ]↑ →
    Γ ⊢ t ∷ B →
    Π-allowed p q →
    Π-allowed 𝟙 (q + p) →
    Γ ⊢ sumrec q p a b A B P l r (inr t) ≡ r [ t ]₀ ∷ P [ inr t ]₀
  ⊢sumrec-inr≡
    {(m)} {(n)} {Γ} {a} {b} {A} {B} {P}
    {l} {r} {t} {p} {q}
    ⊢a ⊢b ⊢A ⊢B ⊢P ⊢l ⊢r ⊢t Π-ok₁ Π-ok₂ =
      let ⊢Γ = wfTerm ⊢t
          Sumᵢ′ = Sumᵢ xa xb xA xB
      in  check-and-equal-type-and-terms-sound
        (γ′ λ where
          .I.equalities → L.[]
          .I.bindings → λ where
            (I.var! x0) → I.base , I.level a
            (I.var! x1) → I.base , I.level b
            (I.var! x2) → I.base , I.term A (I.U xa)
            (I.var! x3) → I.base , I.term B (I.U xb)
            (I.var! x4) → I.base I.∙ Sumᵢ′ , I.type P
            (I.var! x5) →
              I.base I.∙ xA , I.term l (I.subst xP (I.cons (IS.wkSubst 1 I.id)
                (inlᵢ (IW.wk (step id) xa) (IW.wk (step id) xb) (IW.wk (step id) xA) (IW.wk (step id) xB) (I.var x0))))
            (I.var! x6) →
              I.base I.∙ xB , I.term r (I.subst xP (I.cons (IS.wkSubst 1 I.id)
                (inrᵢ (IW.wk (step id) xa) (IW.wk (step id) xb) (IW.wk (step id) xA) (IW.wk (step id) xB) (I.var x0))))
            (I.var! x7) → I.base , I.term t xB
            (I.var not-x8 _))
         (I.base nothing I.» I.base)
         (sumrecᵢ′ xa xb xA xB xP xl xr (inrᵢ xa xb xA xB xt))
         (I.subst xr (IS.sgSubst xt))
         (I.subst xP (IS.sgSubst (inrᵢ xa xb xA xB xt)))
         50
         PE.refl
         (λ where
           .IC.constraints-wf →
             Unit-ok L.∷ Unit-ok L.∷
             Π-ok L.∷ Π-ok₂ L.∷ Π-ok₁ L.∷
             Σ-ok₁ L.∷ Σ-ok₂ L.∷ L.[]
           .IC.metas-wf .IC.equalities-wf → L.[]
           .IC.metas-wf .IC.bindings-wf → λ where
             (I.var! x0) → ⊢a
             (I.var! x1) → ⊢b
             (I.var! x2) → ⊢A
             (I.var! x3) → ⊢B
             (I.var! x4) → ⊢P
             (I.var! x5) → ⊢l
             (I.var! x6) → ⊢r
             (I.var! x7) → ⊢t
             (I.var not-x8 _))
         ⊢Γ

    where
    open Defs′ q p Γ
      (n V.∷ n V.∷ n V.∷ n V.∷ (1+ n) V.∷
      (1+ n) V.∷ (1+ n) V.∷ n V.∷ V.ε)

    xa xb xA xB xt : I.Term c n
    xa = I.varᵐ x0
    xb = I.varᵐ x1
    xA = I.varᵐ x2
    xB = I.varᵐ x3
    xt = I.varᵐ x7

    xP xl xr : I.Term c (1+ n)
    xP = I.varᵐ x4
    xl = I.varᵐ x5
    xr = I.varᵐ x6
