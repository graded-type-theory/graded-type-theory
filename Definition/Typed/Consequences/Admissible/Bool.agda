------------------------------------------------------------------------
-- Typing and equality rules related to Bool
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
import Definition.Untyped.Bool
open import Graded.Modality

module Definition.Typed.Consequences.Admissible.Bool
  {a} {M : Set a}
  {𝕄 : Modality M}
  (open Definition.Untyped.Bool 𝕄)
  (open Modality 𝕄)
  (R : Type-restrictions 𝕄)
  (open Type-restrictions R)
  -- It is assumed that the modality has an nr function.
  ⦃ has-nr : Has-nr M semiring-with-meet ⦄
  -- It is assumed that certain Σ-types are allowed.
  (Σ-ok : Σʷ-allowed ω Boolᵍ)
  -- It is assumed that weak unit types are allowed.
  (Unitʷ-ok : Unitʷ-allowed)
  where

open Internal R

open import Definition.Typed R
open import Definition.Typed.Decidable.Internal R
import Definition.Typed.Decidable.Internal.Context R as IC
import Definition.Typed.Decidable.Internal.Term R as I
import Definition.Typed.Decidable.Internal.Tests R as IT
import Definition.Typed.Decidable.Internal.Substitution R as IS
open import Definition.Typed.Properties.Admissible.Bool.OK
  R Unitʷ-ok
open import Definition.Typed.Properties.Admissible.Level R
open import Definition.Typed.Properties.Admissible.Nat R
open import Definition.Typed.Properties.Admissible.Var R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Reasoning.Type R
open import Definition.Typed.Stability R
open import Definition.Typed.Substitution.Primitive R
open import Definition.Typed.Syntactic R
open import Definition.Typed.Well-formed R

open import Definition.Untyped M
open import Definition.Untyped.Empty 𝕄
open import Definition.Untyped.Nat 𝕄

import Tools.Bool as Bool
open import Tools.Fin
open import Tools.Function
import Tools.List as L
open import Tools.Maybe
open import Tools.Nat using (Nat; 1+)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality
import Tools.Vec as V

private variable
  ∇                                 : DCon (Term 0) _
  k m ms n                          : Nat
  Δ                                 : Con Term _
  Γ                                 : Cons _ _
  A A₁ A₂ B t t₁ t₂ u u₁ u₂ v v₁ v₂ : Term _
  p                                 : M

------------------------------------------------------------------------
-- Typing rules for Bool, true and false

opaque
  unfolding Bool

  -- A typing rule for Bool.

  ⊢Bool∷U :
    ⊢ Γ →
    Γ ⊢ Bool ∷ U zeroᵘ
  ⊢Bool∷U ⊢Γ =
    ΠΣⱼ (⊢zeroᵘ ⊢Γ) (ℕⱼ ⊢Γ) (⊢OK∷U (var₀ (⊢ℕ ⊢Γ))) Σ-ok

opaque

  -- A typing rule for Bool.

  ⊢Bool :
    ⊢ Γ →
    Γ ⊢ Bool
  ⊢Bool = univ ∘→ ⊢Bool∷U

opaque
  unfolding Bool true

  -- A typing rule for true.

  ⊢true :
    ⊢ Γ →
    Γ ⊢ true ∷ Bool
  ⊢true ⊢Γ =
    prodⱼ (⊢OK (var₀ (⊢ℕ ⊢Γ))) (sucⱼ (zeroⱼ ⊢Γ))
      (conv (starⱼ ⊢Γ Unitʷ-ok)
         (Unitʷ                      ≡˘⟨ OK-1≡ ⊢Γ ⟩⊢∎≡
          OK (suc zero)              ≡˘⟨ OK-[] ⟩
          OK (var x0) [ suc zero ]₀  ∎))
      Σ-ok

opaque
  unfolding Bool false

  -- A typing rule for false.

  ⊢false :
    ⊢ Γ →
    Γ ⊢ false ∷ Bool
  ⊢false ⊢Γ =
    prodⱼ (⊢OK (var₀ (⊢ℕ ⊢Γ))) (zeroⱼ ⊢Γ)
      (conv (starⱼ ⊢Γ Unitʷ-ok)
         (Unitʷ                  ≡˘⟨ OK-0≡ ⊢Γ ⟩⊢∎≡
          OK zero                ≡˘⟨ OK-[] ⟩
          OK (var x0) [ zero ]₀  ∎))
      Σ-ok

------------------------------------------------------------------------
-- Typing rules for Target

opaque
  unfolding Bool Target

  -- An equality rule for Target.

  Target-cong :
    ∇ » drop k Δ ∙ Bool ⊢ A₁ ≡ A₂ →
    ∇ » Δ ⊢ t₁ ≡ t₂ ∷ ℕ →
    ∇ » Δ ⊢ u₁ ≡ u₂ ∷ OK t₁ →
    ∇ » Δ ⊢ Target k A₁ t₁ u₁ ≡ Target k A₂ t₂ u₂
  Target-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ =
    [][]↑-cong A₁≡A₂ $
    PE.subst (_⊢_≡_∷_ _ _ _)
      (PE.cong (Σ⟨_⟩_,_▷_▹_ _ _ _ _) $ PE.sym OK-[]) $
    prod-cong (⊢OK (var₀ (⊢ℕ (wfEqTerm t₁≡t₂)))) t₁≡t₂
      (PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym OK-[]) u₁≡u₂)
      Σ-ok

private opaque

  -- A variant of Target-cong.

  Target-cong′ :
    ∇ » drop k Δ ∙ Bool ⊢ A₁ ≡ A₂ →
    ∇ » Δ ⊢ t ∷ ℕ →
    ∇ » Δ ⊢ u ∷ OK t →
    ∇ » Δ ⊢ Target k A₁ t u ≡ Target k A₂ t u
  Target-cong′ A₁≡A₂ ⊢t ⊢u =
    Target-cong A₁≡A₂ (refl ⊢t) (refl ⊢u)

opaque

  -- A typing rule for Target.

  ⊢Target :
    ∇ » drop k Δ ∙ Bool ⊢ A →
    ∇ » Δ ⊢ t ∷ ℕ →
    ∇ » Δ ⊢ u ∷ OK t →
    ∇ » Δ ⊢ Target k A t u
  ⊢Target ⊢A ⊢t ⊢u =
    syntacticEq (Target-cong′ (refl ⊢A) ⊢t ⊢u) .proj₁

------------------------------------------------------------------------
-- Typing rules for boolrec

-- Some definitions used below.

private
  module Defs (p : M) (Γ : Cons m n) (meta-con-size : V.Vec Nat ms)
    where
    c : I.Constants
    c .I.gs               = 7
    c .I.ss               = 0
    c .I.bms              = 0
    c .I.ms               = ms
    c .I.base-dcon-size   = m
    c .I.base-con-size    = n
    c .I.base-con-allowed = Bool.true
    c .I.meta-con-size    = meta-con-size

    xp xBoolᵍ xOKᵍ xboolrecᵍ-Π xboolrecᵍ-nc₁ xboolrecᵍ-nc₂
      xboolrecᵍ-pr : I.Termᵍ 7
    xp            = I.var x0
    xBoolᵍ        = I.var x1
    xOKᵍ          = I.var x2
    xboolrecᵍ-Π   = I.var x3
    xboolrecᵍ-nc₁ = I.var x4
    xboolrecᵍ-nc₂ = I.var x5
    xboolrecᵍ-pr  = I.var x6

    Boolᵢ′ : I.Term c n
    Boolᵢ′ = Boolᵢ xBoolᵍ xOKᵍ

    trueᵢ′ : I.Term c n
    trueᵢ′ = trueᵢ xBoolᵍ xOKᵍ

    falseᵢ′ : I.Term c n
    falseᵢ′ = falseᵢ xBoolᵍ xOKᵍ

    boolrecᵢ′ : I.Term c (1+ n) → (_ _ _ : I.Term c n) → I.Term c n
    boolrecᵢ′ =
      boolrecᵢ xBoolᵍ xOKᵍ xboolrecᵍ-Π xboolrecᵍ-nc₁ xboolrecᵍ-nc₂
        xboolrecᵍ-pr xp

    γ :
      (∀ {n} (x : I.Meta-var c n) → I.Con c n × I.Type-or-term c n) →
      I.Contexts c
    γ _ .I.grades =
      p V.∷ Boolᵍ V.∷ OKᵍ V.∷ boolrecᵍ-Π V.∷ boolrecᵍ-nc₁ V.∷
      boolrecᵍ-nc₂ V.∷ boolrecᵍ-pr V.∷ V.ε
    γ _ .I.strengths           = V.ε
    γ _ .I.binder-modes        = V.ε
    γ _ .I.⌜base⌝              = Γ
    γ Μ .I.metas .I.bindings   = Μ
    γ _ .I.metas .I.equalities = L.[]
    γ _ .I.constraints⁰        = I.emptyᶜ⁰
    γ _ .I.constraints⁺        =
      I.unit-allowed I.𝕤         L.∷
      I.unit-allowed I.𝕨         L.∷
      I.π-allowed xboolrecᵍ-Π xp L.∷
      I.π-allowed I.𝟙 I.𝟘        L.∷
      I.σʷ-allowed I.ω xBoolᵍ    L.∷
      L.[]

    γ′ :
      I.Meta-con c →
      I.Contexts c
    γ′ Μ = record (γ (Μ .I.bindings)) { metas = Μ }

opaque
  unfolding
    Bool OK Target boolrec boolrecᵍ-nc₃ emptyrec-sink false natcase true

  -- An equality rule for boolrec.

  boolrec-cong :
    {Γ : Cons m n} →
    Π-allowed boolrecᵍ-Π p →
    Π-allowed 𝟙 𝟘 →
    Unitˢ-allowed →
    Γ »∙ Bool ⊢ A₁ ≡ A₂ →
    Γ ⊢ t₁ ≡ t₂ ∷ A₁ [ true ]₀ →
    Γ ⊢ u₁ ≡ u₂ ∷ A₁ [ false ]₀ →
    Γ ⊢ v₁ ≡ v₂ ∷ Bool →
    Γ ⊢ boolrec p A₁ t₁ u₁ v₁ ≡ boolrec p A₂ t₂ u₂ v₂ ∷ A₁ [ v₁ ]₀
  boolrec-cong
    {n} {p} {A₁} {A₂} {t₁} {t₂} {u₁} {u₂} {v₁} {v₂} {Γ}
    Π-ok Π-𝟙-𝟘-ok Unitˢ-ok A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ =
    let ⊢A₁ , ⊢A₂     = wf-⊢≡ A₁≡A₂
        _ , ⊢t₁ , ⊢t₂ = wf-⊢≡∷ t₁≡t₂
        _ , ⊢u₁ , ⊢u₂ = wf-⊢≡∷ u₁≡u₂
        _ , ⊢v₁ , ⊢v₂ = wf-⊢≡∷ v₁≡v₂
        ⊢Γ            = wfTerm ⊢t₁
    in
    check-and-equal-type-and-terms-sound
      (γ′ λ where
         .I.equalities →
           (_ , IT.meta xA₁ , IT.meta xA₂) L.∷
           (_ , IT.meta xt₁ , IT.meta xt₂) L.∷
           (_ , IT.meta xu₁ , IT.meta xu₂) L.∷
           (_ , IT.meta xv₁ , IT.meta xv₂) L.∷
           L.[]
         .I.bindings → λ where
           (I.var! x0) → I.base I.∙ Boolᵢ′ , I.type A₁
           (I.var! x1) → I.base I.∙ Boolᵢ′ , I.type A₂
           (I.var! x2) →
             I.base , I.term t₁ (I.subst xA₁ (IS.sgSubst trueᵢ′))
           (I.var! x3) →
             I.base , I.term t₂ (I.subst xA₁ (IS.sgSubst trueᵢ′))
           (I.var! x4) →
             I.base , I.term u₁ (I.subst xA₁ (IS.sgSubst falseᵢ′))
           (I.var! x5) →
             I.base , I.term u₂ (I.subst xA₁ (IS.sgSubst falseᵢ′))
           (I.var! x6) → I.base , I.term v₁ Boolᵢ′
           (I.var! x7) → I.base , I.term v₂ Boolᵢ′
           (I.var not-x8 _))
      (I.base nothing I.» I.base)
      (boolrecᵢ′ xA₁ xt₁ xu₁ xv₁)
      (boolrecᵢ′ xA₂ xt₂ xu₂ xv₂)
      (I.subst xA₁ (IS.sgSubst xv₁))
      33
      PE.refl
      (λ where
         .IC.constraints-wf →
           Unitˢ-ok L.∷ Unitʷ-ok L.∷ Π-ok L.∷ Π-𝟙-𝟘-ok L.∷ Σ-ok L.∷ L.[]
         .IC.metas-wf .IC.equalities-wf →
           (reflConEq (∙ ⊢Bool ⊢Γ) , IC.type A₁≡A₂) L.∷
           (reflConEq ⊢Γ ,
            IC.term (refl (substType ⊢A₁ (⊢true ⊢Γ))) t₁≡t₂) L.∷
           (reflConEq ⊢Γ ,
            IC.term (refl (substType ⊢A₁ (⊢false ⊢Γ))) u₁≡u₂) L.∷
           (reflConEq ⊢Γ , IC.term (refl (⊢Bool ⊢Γ)) v₁≡v₂) L.∷
           L.[]
         .IC.metas-wf .IC.bindings-wf → λ where
           (I.var! x0)       → ⊢A₁
           (I.var! x1)       → ⊢A₂
           (I.var! x2)       → ⊢t₁
           (I.var! x3)       → ⊢t₂
           (I.var! x4)       → ⊢u₁
           (I.var! x5)       → ⊢u₂
           (I.var! x6)       → ⊢v₁
           (I.var! x7)       → ⊢v₂
           (I.var  not-x8 _))
      ⊢Γ
      where
      open Defs p Γ
             (1+ n V.∷ 1+ n V.∷ n V.∷ n V.∷ n V.∷ n V.∷ n V.∷ n V.∷ V.ε)

      xt₁ xt₂ xu₁ xu₂ xv₁ xv₂ : I.Term c n
      xt₁ = I.varᵐ x2
      xt₂ = I.varᵐ x3
      xu₁ = I.varᵐ x4
      xu₂ = I.varᵐ x5
      xv₁ = I.varᵐ x6
      xv₂ = I.varᵐ x7

      xA₁ xA₂ : I.Term c (1+ n)
      xA₁ = I.varᵐ x0
      xA₂ = I.varᵐ x1

opaque

  -- A typing rule for boolrec.

  ⊢boolrec :
    Π-allowed boolrecᵍ-Π p →
    Π-allowed 𝟙 𝟘 →
    Unitˢ-allowed →
    Γ »∙ Bool ⊢ A →
    Γ ⊢ t ∷ A [ true ]₀ →
    Γ ⊢ u ∷ A [ false ]₀ →
    Γ ⊢ v ∷ Bool →
    Γ ⊢ boolrec p A t u v ∷ A [ v ]₀
  ⊢boolrec Π-ok Π-𝟙-𝟘-ok Unitˢ-ok ⊢A ⊢t ⊢u ⊢v =
    syntacticEqTerm
      (boolrec-cong Π-ok Π-𝟙-𝟘-ok Unitˢ-ok (refl ⊢A) (refl ⊢t) (refl ⊢u)
         (refl ⊢v))
      .proj₂ .proj₁

opaque
  unfolding
    Bool OK Target boolrec boolrecᵍ-nc₃ emptyrec-sink false natcase true

  -- An equality rule for boolrec.

  boolrec-true-≡ :
    {Γ : Cons m n} →
    Π-allowed boolrecᵍ-Π p →
    Π-allowed 𝟙 𝟘 →
    Unitˢ-allowed →
    Γ »∙ Bool ⊢ A →
    Γ ⊢ t ∷ A [ true ]₀ →
    Γ ⊢ u ∷ A [ false ]₀ →
    Γ ⊢ boolrec p A t u true ≡ t ∷ A [ true ]₀
  boolrec-true-≡
    {n} {p} {A} {t} {u} {Γ} Π-ok Π-𝟙-𝟘-ok Unitˢ-ok ⊢A ⊢t ⊢u =
    check-and-equal-type-and-terms-sound
      (γ λ where
         (I.var! x0) → I.base I.∙ Boolᵢ′ , I.type A
         (I.var! x1) →
           I.base , I.term t (I.subst xA (IS.sgSubst trueᵢ′))
         (I.var! x2) →
           I.base , I.term u (I.subst xA (IS.sgSubst falseᵢ′))
         (I.var not-x3 _))
      (I.base nothing I.» I.base)
      (boolrecᵢ′ xA xt xu trueᵢ′)
      xt
      (I.subst xA (IS.sgSubst trueᵢ′))
      27
      PE.refl
      (λ where
         .IC.constraints-wf →
           Unitˢ-ok L.∷ Unitʷ-ok L.∷ Π-ok L.∷ Π-𝟙-𝟘-ok L.∷ Σ-ok L.∷ L.[]
         .IC.metas-wf .IC.equalities-wf → L.[]
         .IC.metas-wf .IC.bindings-wf   → λ where
           (I.var! x0)       → ⊢A
           (I.var! x1)       → ⊢t
           (I.var! x2)       → ⊢u
           (I.var  not-x3 _))
      (wfTerm ⊢t)
      where
      open Defs p Γ (1+ n V.∷ n V.∷ n V.∷ V.ε)

      xt xu : I.Term c n
      xt = I.varᵐ x1
      xu = I.varᵐ x2

      xA : I.Term c (1+ n)
      xA = I.varᵐ x0

opaque
  unfolding
    Bool OK Target boolrec boolrecᵍ-nc₃ emptyrec-sink false natcase true

  -- An equality rule for boolrec.

  boolrec-false-≡ :
    {Γ : Cons m n} →
    Π-allowed boolrecᵍ-Π p →
    Π-allowed 𝟙 𝟘 →
    Unitˢ-allowed →
    Γ »∙ Bool ⊢ A →
    Γ ⊢ t ∷ A [ true ]₀ →
    Γ ⊢ u ∷ A [ false ]₀ →
    Γ ⊢ boolrec p A t u false ≡ u ∷ A [ false ]₀
  boolrec-false-≡
    {n} {p} {A} {t} {u} {Γ} Π-ok Π-𝟙-𝟘-ok Unitˢ-ok ⊢A ⊢t ⊢u =
    check-and-equal-type-and-terms-sound
      (γ λ where
         (I.var! x0) → I.base I.∙ Boolᵢ′ , I.type A
         (I.var! x1) →
           I.base , I.term t (I.subst xA (IS.sgSubst trueᵢ′))
         (I.var! x2) →
           I.base , I.term u (I.subst xA (IS.sgSubst falseᵢ′))
         (I.var not-x3 _))
      (I.base nothing I.» I.base)
      (boolrecᵢ′ xA xt xu falseᵢ′)
      xu
      (I.subst xA (IS.sgSubst falseᵢ′))
      27
      PE.refl
      (λ where
         .IC.constraints-wf →
           Unitˢ-ok L.∷ Unitʷ-ok L.∷ Π-ok L.∷ Π-𝟙-𝟘-ok L.∷ Σ-ok L.∷ L.[]
         .IC.metas-wf .IC.equalities-wf → L.[]
         .IC.metas-wf .IC.bindings-wf   → λ where
           (I.var! x0)       → ⊢A
           (I.var! x1)       → ⊢t
           (I.var! x2)       → ⊢u
           (I.var  not-x3 _))
      (wfTerm ⊢t)
      where
      open Defs p Γ (1+ n V.∷ n V.∷ n V.∷ V.ε)

      xt xu : I.Term c n
      xt = I.varᵐ x1
      xu = I.varᵐ x2

      xA : I.Term c (1+ n)
      xA = I.varᵐ x0
