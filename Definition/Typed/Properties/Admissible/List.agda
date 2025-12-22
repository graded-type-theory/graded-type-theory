------------------------------------------------------------------------
-- Typing and equality rules related to List
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
import Definition.Untyped
open import Graded.Modality

module Definition.Typed.Properties.Admissible.List
  {a} {M : Set a}
  {𝕄 : Modality M}
  (open Definition.Untyped M)
  (pₕ pₗ : M)
  (open Modality 𝕄)
  (R : Type-restrictions 𝕄)
  (open Type-restrictions R)
  -- It is assumed that a certain unit type is allowed.
  (Unit-ok : Unitʷ-allowed)
  -- It is assumed that certain Σ-types are allowed
  (Σ-ok₁ : Σʷ-allowed pₕ 𝟘)
  (Σ-ok₂ : Σʷ-allowed pₗ 𝟙)
  where

open import Definition.Typed R
open import Definition.Typed.Decidable.Internal R
import Definition.Typed.Decidable.Internal.Context R as IC
import Definition.Typed.Decidable.Internal.Term 𝕄 as I
import Definition.Typed.Decidable.Internal.Substitution 𝕄 as IS
import Definition.Typed.Decidable.Internal.Weakening 𝕄 as IW
open import Definition.Typed.Properties R
open import Definition.Typed.Stability R
open import Definition.Typed.Well-formed R

open import Definition.Untyped.List 𝕄 pₕ pₗ
import Definition.Untyped.Vec 𝕄 𝕨 pₕ as UV

open import Tools.Bool
open import Tools.Fin
import Tools.List as L
open import Tools.Maybe
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
import Tools.Vec as V

private variable
  m ms n                            : Nat
  A A₁ A₂ B t t₁ t₂ u u₁ u₂ v w₁ w₂ : Term _
  Γ                                 : Cons _ _
  l                                 : Universe-level
  p₁ p₂ q r₁ r₂                     : M

-- Some definitions used below.

private
  module Defs
    (p₁ p₂ q r₁ r₂ : M) (l : Universe-level) (Γ : Cons m n)
    (meta-con-size : V.Vec Nat ms)
    where
    c : I.Constants
    c .I.gs               = 7
    c .I.ls               = 1
    c .I.ss               = 0
    c .I.bms              = 0
    c .I.ms               = ms
    c .I.base-dcon-size   = m
    c .I.base-con-size    = n
    c .I.base-con-allowed = true
    c .I.meta-con-size    = meta-con-size

    xl : I.Termˡ 1
    xl = I.var x0

    xpₕ xpₗ xp₁ xp₂ xq xr₁ xr₂ : I.Termᵍ 7
    xpₕ = I.var x0
    xpₗ = I.var x1
    xp₁ = I.var x2
    xp₂ = I.var x3
    xq  = I.var x4
    xr₁ = I.var x5
    xr₂ = I.var x6

    γ :
      L.List (I.Constraint c) →
      (∀ {n} (x : I.Meta-var c n) → I.Con c n × I.Type-or-term c n) →
      I.Contexts c
    γ _  _ .I.grades              = pₕ V.∷ pₗ V.∷ p₁ V.∷ p₂ V.∷ q V.∷
                                    r₁ V.∷ r₂ V.∷ V.ε
    γ _  _ .I.levels              = l V.∷ V.ε
    γ _  _ .I.strengths           = V.ε
    γ _  _ .I.binder-modes        = V.ε
    γ _  _ .I.⌜base⌝              = Γ
    γ _  Μ .I.metas .I.bindings   = Μ
    γ _  _ .I.metas .I.equalities = L.[]
    γ cs _ .I.constraints         =
      cs L.++
      I.unit-allowed I.𝕨    L.∷
      I.σʷ-allowed xpₕ I.𝟘  L.∷
      I.σʷ-allowed xpₗ I.𝟙  L.∷
      L.[]

    γ′ :
      L.List (I.Constraint c) →
      I.Meta-con c →
      I.Contexts c
    γ′ cs Μ = record (γ cs (Μ .I.bindings)) { metas = Μ }

------------------------------------------------------------------------
-- Some admissible typing and equality rules for List

opaque
  unfolding List UV.Vec′

  -- An equality rule for List.

  List-cong :
    {Γ : Cons m n} →
    Γ ⊢ A₁ ≡ A₂ ∷ U l →
    Γ ⊢ List l A₁ ≡ List l A₂ ∷ U l
  List-cong {n} {A₁} {A₂} {l} {Γ} A₁≡A₂ =
    let _ , ⊢A₁ , ⊢A₂ = wf-⊢≡∷ A₁≡A₂
        ⊢Γ            = wfTerm ⊢A₁
    in
    check-and-equal-type-and-terms-sound
      (γ′ L.[] λ where
         .I.equalities →
           (_ , I.var! x0 , I.var! x1) L.∷
           L.[]
         .I.bindings → λ where
           (I.var! x0)      → I.base , I.term A₁ (I.U xl)
           (I.var! x1)      → I.base , I.term A₂ (I.U xl)
           (I.var not-x2 _))
      (I.base nothing I.» I.base)
      (Listᵢ xpₕ xpₗ xl xA₁)
      (Listᵢ xpₕ xpₗ xl xA₂)
      (I.U xl)
      9
      PE.refl
      (λ where
         .IC.constraints-wf →
           Unit-ok L.∷ Σ-ok₁ L.∷ Σ-ok₂ L.∷ L.[]
         .IC.metas-wf .IC.equalities-wf →
           (reflConEq ⊢Γ , IC.term (refl (Uⱼ ⊢Γ)) A₁≡A₂) L.∷
           L.[]
         .IC.metas-wf .IC.bindings-wf   → λ where
           (I.var! x0)       → ⊢A₁
           (I.var! x1)       → ⊢A₂
           (I.var  not-x2 _))
      ⊢Γ
      where
      open Defs pₕ pₕ pₕ pₕ pₕ l Γ (n V.∷ n V.∷ V.ε)

      xA₁ xA₂ : I.Term c n
      xA₁ = I.varᵐ x0
      xA₂ = I.varᵐ x1

opaque

  -- A typing rule for List.

  ⊢List :
    {Γ : Cons m n} →
    Γ ⊢ A ∷ U l →
    Γ ⊢ List l A ∷ U l
  ⊢List ⊢A =
    wf-⊢≡∷ (List-cong (refl ⊢A)) .proj₂ .proj₁

------------------------------------------------------------------------
-- An admissible typing rule for nil

opaque
  unfolding List UV.Vec′ nil UV.nil′

  -- A typing rule for nil.

  ⊢nil :
    {Γ : Cons m n} →
    Γ ⊢ A ∷ U l →
    Γ ⊢ nil l A ∷ List l A
  ⊢nil {n} {A} {l} {Γ} ⊢A =
    check-type-and-term-sound
      (γ L.[] λ where
         (I.var! x0)      → I.base , I.term A (I.U xl)
         (I.var not-x1 _))
      (I.base nothing I.» I.base)
      (nilᵢ xpₗ xpₕ xl xA)
      (Listᵢ xpₕ xpₗ xl xA)
      13
      PE.refl
      (λ where
         .IC.constraints-wf →
           Unit-ok L.∷ Σ-ok₁ L.∷ Σ-ok₂ L.∷ L.[]
         .IC.metas-wf .IC.equalities-wf → L.[]
         .IC.metas-wf .IC.bindings-wf   → λ where
           (I.var! x0)       → ⊢A
           (I.var  not-x1 _))
      (wfTerm ⊢A)
      where
      open Defs pₕ pₕ pₕ pₕ pₕ l Γ (n V.∷ V.ε)

      xA : I.Term c n
      xA = I.varᵐ x0

------------------------------------------------------------------------
-- Some admissible typing and equality rules for cons

opaque
  unfolding List UV.Vec′ cons UV.cons′

  -- An equality rule for cons.

  cons-cong :
    {Γ : Cons m n} →
    Γ ⊢ A₁ ≡ A₂ ∷ U l →
    Γ ⊢ t₁ ≡ t₂ ∷ A₁ →
    Γ ⊢ u₁ ≡ u₂ ∷ List l A₁ →
    Γ ⊢ cons l A₁ t₁ u₁ ≡ cons l A₂ t₂ u₂ ∷ List l A₁
  cons-cong
    {n} {A₁} {A₂} {l} {t₁} {t₂} {u₁} {u₂} {Γ} A₁≡A₂ t₁≡t₂ u₁≡u₂ =
    let _ , ⊢A₁ , ⊢A₂ = wf-⊢≡∷ A₁≡A₂
        _ , ⊢t₁ , ⊢t₂ = wf-⊢≡∷ t₁≡t₂
        _ , ⊢u₁ , ⊢u₂ = wf-⊢≡∷ u₁≡u₂
        ⊢Γ            = wfTerm ⊢A₁
    in
    check-and-equal-type-and-terms-sound
      (γ′ L.[] λ where
         .I.equalities →
           (_ , I.var! x0 , I.var! x1) L.∷
           (_ , I.var! x2 , I.var! x3) L.∷
           (_ , I.var! x4 , I.var! x5) L.∷
           L.[]
         .I.bindings → λ where
           (I.var! x0)      → I.base , I.term A₁ (I.U xl)
           (I.var! x1)      → I.base , I.term A₂ (I.U xl)
           (I.var! x2)      → I.base , I.term t₁ xA₁
           (I.var! x3)      → I.base , I.term t₂ xA₁
           (I.var! x4)      → I.base , I.term u₁ (Listᵢ xpₕ xpₗ xl xA₁)
           (I.var! x5)      → I.base , I.term u₂ (Listᵢ xpₕ xpₗ xl xA₁)
           (I.var not-x6 _))
      (I.base nothing I.» I.base)
      (consᵢ xpₕ xpₗ xl xA₁ xt₁ xu₁)
      (consᵢ xpₕ xpₗ xl xA₂ xt₂ xu₂)
      (Listᵢ xpₕ xpₗ xl xA₁)
      17
      PE.refl
      (λ where
         .IC.constraints-wf →
           Unit-ok L.∷ Σ-ok₁ L.∷ Σ-ok₂ L.∷ L.[]
         .IC.metas-wf .IC.equalities-wf →
           (reflConEq ⊢Γ , IC.term (refl (Uⱼ ⊢Γ))            A₁≡A₂) L.∷
           (reflConEq ⊢Γ , IC.term (refl (univ ⊢A₁))         t₁≡t₂) L.∷
           (reflConEq ⊢Γ , IC.term (refl (univ (⊢List ⊢A₁))) u₁≡u₂) L.∷
           L.[]
         .IC.metas-wf .IC.bindings-wf   → λ where
           (I.var! x0)       → ⊢A₁
           (I.var! x1)       → ⊢A₂
           (I.var! x2)       → ⊢t₁
           (I.var! x3)       → ⊢t₂
           (I.var! x4)       → ⊢u₁
           (I.var! x5)       → ⊢u₂
           (I.var  not-x6 _))
      ⊢Γ
      where
      open Defs pₕ pₕ pₕ pₕ pₕ l Γ
             (n V.∷ n V.∷ n V.∷ n V.∷ n V.∷ n V.∷ V.ε)

      xA₁ xA₂ xt₁ xt₂ xu₁ xu₂ : I.Term c n
      xA₁ = I.varᵐ x0
      xA₂ = I.varᵐ x1
      xt₁ = I.varᵐ x2
      xt₂ = I.varᵐ x3
      xu₁ = I.varᵐ x4
      xu₂ = I.varᵐ x5

opaque

  -- A typing rule for cons.

  ⊢cons :
    Γ ⊢ A ∷ U l →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ List l A →
    Γ ⊢ cons l A t u ∷ List l A
  ⊢cons ⊢A ⊢t ⊢u =
    wf-⊢≡∷ (cons-cong (refl ⊢A) (refl ⊢t) (refl ⊢u)) .proj₂ .proj₁

------------------------------------------------------------------------
-- Some admissible typing and equality rules for listrec

opaque
  unfolding
    List UV.Vec′ cons UV.cons′ listrec nil UV.nil′
    UV.vecrec′ UV.vecrec-nil UV.vecrec-cons

  -- A typing rule for listrec.

  ⊢listrec :
    {Γ : Cons m n} →
    Π-allowed r₂ q →
    Γ ⊢ A ∷ U l →
    Γ »∙ List l A ⊢ B →
    Γ ⊢ t ∷ B [ nil l A ]₀ →
    Γ »∙ A »∙ wk1 (List l A) »∙ B [ var x0 ]↑² ⊢ u ∷
      B [ 3 ][ cons l (wk[ 3 ]′ A) (var x2) (var x1) ]↑ →
    Γ ⊢ v ∷ List l A →
    Γ ⊢ listrec l r₁ r₂ p₁ p₂ q A B t u v ∷ B [ v ]₀
  ⊢listrec
    {n} {r₂} {q} {A} {l} {B} {t} {u} {v} {r₁} {p₁} {p₂} {Γ}
    Π-ok ⊢A ⊢B ⊢t ⊢u ⊢v =
    check-type-and-term-sound
      (γ (I.π-allowed xr₂ xq L.∷ L.[]) λ where
         (I.var! x0) → I.base , I.term A (I.U xl)
         (I.var! x1) →
           I.base I.∙ Listᵢ xpₕ xpₗ xl xA , I.type B
         (I.var! x2) →
           I.base ,
           I.term t (I.subst xB (IS.sgSubst (nilᵢ xpₗ xpₕ xl xA)))
         (I.var! x3) →
           I.base I.∙ xA I.∙ IW.wk[ 1 ] (Listᵢ xpₕ xpₗ xl xA) I.∙
             I.subst xB (I.cons (IS.wkSubst 2 I.id) (I.var x0)) ,
           I.term u
             (I.subst xB
                (I.cons (IS.wkSubst 3 I.id)
                   (consᵢ xpₕ xpₗ xl (IW.wk[ 3 ] xA) (I.var x2)
                      (I.var x1))))
         (I.var! x4) → I.base , I.term v (Listᵢ xpₕ xpₗ xl xA)
         (I.var not-x5 _))
      (I.base nothing I.» I.base)
      (listrecᵢ xl xpₕ xpₗ xr₁ xr₂ xp₁ xp₂ xq xA xB xt xu xv)
      (I.subst xB (IS.sgSubst xv))
      27
      PE.refl
      (λ where
         .IC.constraints-wf →
           Π-ok L.∷ Unit-ok L.∷ Σ-ok₁ L.∷ Σ-ok₂ L.∷ L.[]
         .IC.metas-wf .IC.equalities-wf → L.[]
         .IC.metas-wf .IC.bindings-wf   → λ where
           (I.var! x0)       → ⊢A
           (I.var! x1)       → ⊢B
           (I.var! x2)       → ⊢t
           (I.var! x3)       → ⊢u
           (I.var! x4)       → ⊢v
           (I.var  not-x5 _))
      (wfTerm ⊢A)
      where
      open Defs p₁ p₂ q r₁ r₂ l Γ
             (n V.∷ 1+ n V.∷ n V.∷ 3+ n V.∷ n V.∷ V.ε)

      xA xt xv : I.Term c n
      xA = I.varᵐ x0
      xt = I.varᵐ x2
      xv = I.varᵐ x4

      xB : I.Term c (1+ n)
      xB = I.varᵐ x1

      xu : I.Term c (3+ n)
      xu = I.varᵐ x3

opaque
  unfolding
    List UV.Vec′ cons UV.cons′ listrec nil UV.nil′
    UV.vecrec′ UV.vecrec-nil UV.vecrec-cons

  -- An equality rule for listrec.

  ⊢listrec-nil≡ :
    {Γ : Cons m n} →
    Π-allowed r₂ q →
    Γ ⊢ A ∷ U l →
    Γ »∙ List l A ⊢ B →
    Γ ⊢ t ∷ B [ nil l A ]₀ →
    Γ »∙ A »∙ wk1 (List l A) »∙ B [ var x0 ]↑² ⊢ u ∷
      B [ 3 ][ cons l (wk[ 3 ]′ A) (var x2) (var x1) ]↑ →
    Γ ⊢ listrec l r₁ r₂ p₁ p₂ q A B t u (nil l A) ≡ t ∷ B [ nil l A ]₀
  ⊢listrec-nil≡
    {n} {r₂} {q} {A} {l} {B} {t} {u} {r₁} {p₁} {p₂} {Γ}
    Π-ok ⊢A ⊢B ⊢t ⊢u =
    check-and-equal-type-and-terms-sound
      (γ (I.π-allowed xr₂ xq L.∷ L.[]) λ where
         (I.var! x0) → I.base , I.term A (I.U xl)
         (I.var! x1) →
           I.base I.∙ Listᵢ xpₕ xpₗ xl xA , I.type B
         (I.var! x2) →
           I.base ,
           I.term t (I.subst xB (IS.sgSubst (nilᵢ xpₗ xpₕ xl xA)))
         (I.var! x3) →
           I.base I.∙ xA I.∙ IW.wk[ 1 ] (Listᵢ xpₕ xpₗ xl xA) I.∙
             I.subst xB (I.cons (IS.wkSubst 2 I.id) (I.var x0)) ,
           I.term u
             (I.subst xB
                (I.cons (IS.wkSubst 3 I.id)
                   (consᵢ xpₕ xpₗ xl (IW.wk[ 3 ] xA) (I.var x2)
                      (I.var x1))))
         (I.var not-x4 _))
      (I.base nothing I.» I.base)
      (listrecᵢ xl xpₕ xpₗ xr₁ xr₂ xp₁ xp₂ xq xA xB xt xu
         (nilᵢ xpₗ xpₕ xl xA))
      xt
      (I.subst xB (IS.sgSubst (nilᵢ xpₗ xpₕ xl xA)))
      28
      PE.refl
      (λ where
         .IC.constraints-wf →
           Π-ok L.∷ Unit-ok L.∷ Σ-ok₁ L.∷ Σ-ok₂ L.∷ L.[]
         .IC.metas-wf .IC.equalities-wf → L.[]
         .IC.metas-wf .IC.bindings-wf   → λ where
           (I.var! x0)       → ⊢A
           (I.var! x1)       → ⊢B
           (I.var! x2)       → ⊢t
           (I.var! x3)       → ⊢u
           (I.var  not-x4 _))
      (wfTerm ⊢A)
      where
      open Defs p₁ p₂ q r₁ r₂ l Γ (n V.∷ 1+ n V.∷ n V.∷ 3+ n V.∷ V.ε)

      xA xt : I.Term c n
      xA = I.varᵐ x0
      xt = I.varᵐ x2

      xB : I.Term c (1+ n)
      xB = I.varᵐ x1

      xu : I.Term c (3+ n)
      xu = I.varᵐ x3

opaque
  unfolding
    List UV.Vec′ cons UV.cons′ listrec nil UV.nil′
    UV.vecrec′ UV.vecrec-nil UV.vecrec-cons

  -- An equality rule for listrec.
  --
  -- Note that the list w has been "η-expanded".

  ⊢listrec-cons≡ :
    {Γ : Cons m n} →
    Π-allowed r₂ q →
    Γ ⊢ A ∷ U l →
    Γ »∙ List l A ⊢ B →
    Γ ⊢ t ∷ B [ nil l A ]₀ →
    Γ »∙ A »∙ wk1 (List l A) »∙ B [ var x0 ]↑² ⊢ u ∷
      B [ 3 ][ cons l (wk[ 3 ]′ A) (var x2) (var x1) ]↑ →
    Γ ⊢ v ∷ A →
    Γ ⊢ w₁ ∷ ℕ →
    Γ ⊢ w₂ ∷ UV.Vec′ l A w₁ →
    let w = prodʷ pₗ w₁ w₂ in
    Γ ⊢ listrec l r₁ r₂ p₁ p₂ q A B t u (cons l A v w) ≡
      u [ consSubst (consSubst (sgSubst v) w)
            (listrec l r₁ r₂ p₁ p₂ q A B t u w) ] ∷
      B [ cons l A v w ]₀
  ⊢listrec-cons≡
    {n} {r₂} {q} {A} {l} {B} {t} {u} {v} {w₁} {w₂} {r₁} {p₁} {p₂} {Γ}
    Π-ok ⊢A ⊢B ⊢t ⊢u ⊢v ⊢w₁ ⊢w₂ =
    check-and-equal-type-and-terms-sound
      (γ (I.π-allowed xr₂ xq L.∷ L.[]) λ where
         (I.var! x0) → I.base , I.term A (I.U xl)
         (I.var! x1) →
           I.base I.∙ Listᵢ xpₕ xpₗ xl xA , I.type B
         (I.var! x2) →
           I.base ,
           I.term t (I.subst xB (IS.sgSubst (nilᵢ xpₗ xpₕ xl xA)))
         (I.var! x3) →
           I.base I.∙ xA I.∙ IW.wk[ 1 ] (Listᵢ xpₕ xpₗ xl xA) I.∙
             I.subst xB (I.cons (IS.wkSubst 2 I.id) (I.var x0)) ,
           I.term u
             (I.subst xB
                (I.cons (IS.wkSubst 3 I.id)
                   (consᵢ xpₕ xpₗ xl (IW.wk[ 3 ] xA) (I.var x2)
                      (I.var x1))))
         (I.var! x4) → I.base , I.term v xA
         (I.var! x5) → I.base , I.term w₁ I.ℕ
         (I.var! x6) → I.base , I.term w₂ (UV.Vec′ᵢ I.𝕨 xpₕ xl xA xw₁)
         (I.var not-x7 _))
      (I.base nothing I.» I.base)
      (listrecᵢ xl xpₕ xpₗ xr₁ xr₂ xp₁ xp₂ xq xA xB xt xu
         (consᵢ xpₕ xpₗ xl xA xv xw))
      (I.subst xu
         (I.cons (I.cons (IS.sgSubst xv) xw)
            (listrecᵢ xl xpₕ xpₗ xr₁ xr₂ xp₁ xp₂ xq xA xB xt xu xw)))
      (I.subst xB (IS.sgSubst (consᵢ xpₕ xpₗ xl xA xv xw)))
      34
      PE.refl
      (λ where
         .IC.constraints-wf →
           Π-ok L.∷ Unit-ok L.∷ Σ-ok₁ L.∷ Σ-ok₂ L.∷ L.[]
         .IC.metas-wf .IC.equalities-wf → L.[]
         .IC.metas-wf .IC.bindings-wf   → λ where
           (I.var! x0)       → ⊢A
           (I.var! x1)       → ⊢B
           (I.var! x2)       → ⊢t
           (I.var! x3)       → ⊢u
           (I.var! x4)       → ⊢v
           (I.var! x5)       → ⊢w₁
           (I.var! x6)       → ⊢w₂
           (I.var  not-x7 _))
      (wfTerm ⊢A)
      where
      open Defs p₁ p₂ q r₁ r₂ l Γ
             (n V.∷ 1+ n V.∷ n V.∷ 3+ n V.∷ n V.∷ n V.∷ n V.∷ V.ε)

      xA xt xv xw₁ xw₂ xw : I.Term c n
      xA  = I.varᵐ x0
      xt  = I.varᵐ x2
      xv  = I.varᵐ x4
      xw₁ = I.varᵐ x5
      xw₂ = I.varᵐ x6
      xw  =
        I.prod I.𝕨 xpₗ
          (just (I.𝟙 , UV.Vec′ᵢ I.𝕨 xpₕ xl (IW.wk[ 1 ] xA) (I.var x0)))
          xw₁ xw₂

      xB : I.Term c (1+ n)
      xB = I.varᵐ x1

      xu : I.Term c (3+ n)
      xu = I.varᵐ x3
