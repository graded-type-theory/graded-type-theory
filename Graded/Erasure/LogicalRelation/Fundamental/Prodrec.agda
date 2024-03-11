------------------------------------------------------------------------
-- Graded.Erasure validity of prodrec.
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

open import Definition.Typed.Restrictions
open import Graded.Erasure.LogicalRelation.Assumptions
open import Graded.Modality

module Graded.Erasure.LogicalRelation.Fundamental.Prodrec
  {a} {M : Set a}
  {𝕄 : Modality M}
  (open Modality 𝕄)
  {R : Type-restrictions 𝕄}
  (as : Assumptions R)
  ⦃ 𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet ⦄
  where

open Assumptions as
open Type-restrictions R

open import Definition.Untyped M hiding (_∷_)
open import Definition.Untyped.Properties M
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.RedSteps R
open import Definition.Typed.Weakening R
open import Definition.Typed.Consequences.Substitution R
open import Definition.Typed.Consequences.RedSteps R
open import Definition.Typed.Consequences.Reduction R

open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Properties.Escape R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.Escape R
open import Definition.LogicalRelation.Substitution.Properties R
open import Definition.LogicalRelation.Substitution.Introductions.Pi R
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst R

import Definition.LogicalRelation.Irrelevance R as I
import Definition.LogicalRelation.Weakening R as W
import Definition.LogicalRelation.Substitution.Irrelevance R as IS

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum hiding (id; sym)

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Modality.Properties 𝕄
open import Graded.Mode 𝕄

open import Graded.Erasure.LogicalRelation is-𝟘? as
open import Graded.Erasure.LogicalRelation.Conversion is-𝟘? as
open import Graded.Erasure.LogicalRelation.Reduction is-𝟘? as
open import Graded.Erasure.LogicalRelation.Subsumption is-𝟘? as
open import Graded.Erasure.LogicalRelation.Irrelevance is-𝟘? as
open import Graded.Erasure.LogicalRelation.Value is-𝟘? as

open import Graded.Erasure.Extraction 𝕄 is-𝟘?
open import Graded.Erasure.Extraction.Properties 𝕄
import Graded.Erasure.Target as T
  renaming (_[_,_] to _[_,_]₁₀)
import Graded.Erasure.Target.Properties as TP
open import Graded.Erasure.Target.Reasoning


private
  variable
    n : Nat
    Γ : Con Term n
    A F t u : Term n
    t₁ t₂ : Term n
    v₁ v₂ : T.Term n
    G : Term (1+ n)
    p q q′ r : M
    γ δ : Conₘ n
    σ : Subst k n
    σ′ : T.Subst k n
    m : Mode
    l : TypeLevel

private opaque

  -- A lemma that is used below.

  [liftSubst-sgSubst][liftSubst][]₀≡ :
    (v : T.Term (2+ n)) →
    v T.[ T.liftSubst (T.sgSubst v₁) ] T.[ T.liftSubst σ′ ] T.[ v₂ ]₀
      PE.≡
    v T.[ T.consSubst (T.consSubst σ′ (v₁ T.[ σ′ ])) v₂ ]
  [liftSubst-sgSubst][liftSubst][]₀≡ {v₁} {σ′} {v₂} v =
    v T.[ T.liftSubst (T.sgSubst v₁) ] T.[ T.liftSubst σ′ ] T.[ v₂ ]₀  ≡⟨ PE.cong T._[ _ ]₀ $ TP.subst-liftSubst-sgSubst v ⟩

    v T.[ T.liftSubstn σ′ 2 ]
      T.[ T.liftSubst (T.sgSubst (v₁ T.[ σ′ ])) ] T.[ v₂ ]₀            ≡⟨ TP.singleSubstComp _ _ (v T.[ _ ]) ⟩

    v T.[ T.liftSubstn σ′ 2 ] T.[ v₁ T.[ σ′ ] , v₂ ]₁₀                 ≡⟨ TP.doubleSubstComp v _ _ _ ⟩

    v T.[ T.consSubst (T.consSubst σ′ (v₁ T.[ σ′ ])) v₂ ]              ∎
    where
    open Tools.Reasoning.PropositionalEquality

prodrecωʳ′-𝟘 :
  {Γ : Con Term n}
  ([Γ] : ⊩ᵛ Γ)
  ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
  ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
  (ok : Σʷ-allowed p q) →
  Γ ∙ (Σʷ p , q ▷ F ▹ G) ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ Σᵛ [Γ] [F] [G] ok →
  ([A₊] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ A [ prodʷ p (var x1) (var x0) ]↑² /
            [Γ] ∙ [F] ∙ [G]) →
  δ ∙ (r · p) ∙ r ▸ Γ ∙ F ∙ G ⊩ʳ⟨ l ⟩ u ∷[ 𝟙ᵐ ]
    A [ prodʷ p (var x1) (var x0) ]↑² / [Γ] ∙ [F] ∙ [G] / [A₊] →
  ([At] : Γ ⊩ᵛ⟨ l ⟩ A [ t ]₀ / [Γ]) →
  Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ u ∷ A [ prodʷ p (var x1) (var x0) ]↑² /
    [Γ] ∙ [F] ∙ [G] / [A₊] →
  ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ) →
  σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ r ·ᶜ γ +ᶜ δ / [Γ] / [σ] →
  ([t₁] : Δ ⊩⟨ l ⟩ t₁ ∷ F [ σ ] / [F] .unwrap ⊢Δ [σ] .proj₁) →
  Δ ⊩⟨ l ⟩ t₂ ∷ G [ consSubst σ t₁ ] /
    [G] .unwrap ⊢Δ ([σ] , [t₁]) .proj₁ →
  Δ ⊢ t [ σ ] ⇒* prodʷ p t₁ t₂ ∷ Σʷ p , q ▷ F ▹ G [ σ ] →
  erase str t T.[ σ′ ] T.⇒* v₂ →
  t₂ ®⟨ l ⟩ v₂ ∷ G [ consSubst σ t₁ ] /
    [G] .unwrap ⊢Δ ([σ] , [t₁]) .proj₁ →
  p PE.≡ 𝟘 → r PE.≢ 𝟘 →
  prodrec r p q′ A t u [ σ ] ®⟨ l ⟩
    erase str (prodrec r p q′ A t u) T.[ σ′ ] ∷ A [ t ]₀ [ σ ] /
    [At] .unwrap ⊢Δ [σ] .proj₁
prodrecωʳ′-𝟘
  {G} {p} {A} {δ} {r} {u} {t} {σ} {σ′} {γ} {t₁} {t₂}
  [Γ] [F] [G] ok [A] [A₊] ⊩ʳu [At] [u] [σ] σ®σ′ [t₁] [t₂] d d′ t₂®v₂
  p≡𝟘 r≢𝟘
  with is-𝟘? r
... | yes r≡𝟘 = ⊥-elim (r≢𝟘 r≡𝟘)
... | no _ with is-𝟘? p
... | no p≢𝟘 = ⊥-elim (p≢𝟘 p≡𝟘)
... | yes PE.refl =
  convTermʳ [σ₊A₊] [σAt] (sym At≡Ap′) pr®pr′
  where
  open Tools.Reasoning.PropositionalEquality

  σ₊     = consSubst (consSubst σ t₁) t₂
  [σ₊]   = ([σ] , [t₁]) , [t₂]
  [σ₊A₊] = [A₊] .unwrap {σ = σ₊} ⊢Δ [σ₊] .proj₁
  [σF]   = [F] .unwrap ⊢Δ [σ] .proj₁
  ⊢σF    = escape [σF]
  [⇑σ]   = liftSubstS [Γ] ⊢Δ [F] [σ]
  [σG]   = [G] .unwrap {σ = liftSubst σ} (⊢Δ ∙ ⊢σF) [⇑σ] .proj₁
  ⊢σG    = escape [σG]
  [σGt₁] = [G] .unwrap ⊢Δ ([σ] , [t₁]) .proj₁
  [Σ]    = Σᵛ [Γ] [F] [G] _
  [σΣ]   = [Σ] .unwrap ⊢Δ [σ] .proj₁
  ⊢σΣ    = escape [σΣ]
  [σA]   = [A] .unwrap {σ = liftSubst σ} (⊢Δ ∙ ⊢σΣ)
             (liftSubstS [Γ] ⊢Δ [Σ] [σ]) .proj₁
  ⊢σA    = escape [σA]
  [σAt]  = [At] .unwrap ⊢Δ [σ] .proj₁
  [⇑²σ]  = liftSubstS {σ = liftSubst σ} ([Γ] ∙ [F]) (⊢Δ ∙ ⊢σF) [G] [⇑σ]
  [σA₊]  = [A₊] .unwrap {σ = liftSubstn σ 2} (⊢Δ ∙ ⊢σF ∙ ⊢σG) [⇑²σ]
             .proj₁
  [σu]   = [u] {σ = liftSubstn σ 2} (⊢Δ ∙ ⊢σF ∙ ⊢σG) [⇑²σ] .proj₁
  ⊢σu    = escapeTerm [σA₊] [σu]
  ⊢σu′   = PE.subst (λ x → _ ⊢ u [ liftSubstn σ 2 ] ∷ x)
             (subst-β-prodrec A σ) ⊢σu
  ⊢t₁    = escapeTerm [σF] [t₁]
  ⊢t₂    = escapeTerm [σGt₁] [t₂]
  ⊢t₂′   = PE.subst (λ x → Δ ⊢ t₂ ∷ x) (PE.sym (singleSubstComp t₁ σ G))
             ⊢t₂
  At≡Ap  = substTypeEq (refl ⊢σA) (subset*Term d)
  At≡Ap′ = PE.subst₂ (λ x y → Δ ⊢ x ≡ y)
             (PE.sym (singleSubstLift A t))
             (substCompProdrec A t₁ t₂ σ)
             At≡Ap
  red₁   = prodrec-subst* {r = r} d ⊢σF ⊢σG ⊢σA ⊢σu′
  red₂   = prodrec-β ⊢σF ⊢σG ⊢σA ⊢t₁ ⊢t₂′ ⊢σu′ PE.refl ok
  red′   = PE.subst₂ (λ x y → Δ ⊢ _ ⇒* x ∷ y)
             (doubleSubstComp u t₁ t₂ σ)
             (substCompProdrec A t₁ t₂ σ)
             (conv* red₁ At≡Ap ⇨∷* redMany red₂)
  red″ :
    ∃ λ v₂′ → erase str t T.[ σ′ ] T.⇒* v₂′ ×
    T.lam (erase str u T.[ T.liftSubst (T.sgSubst T.↯) ]
             T.[ T.liftSubst σ′ ])
      T.∘⟨ str ⟩ (erase str t T.[ σ′ ]) T.⇒*
    erase str u
      T.[ T.consSubst (T.consSubst σ′ T.↯) v₂′ ]
  red″ =
    case PE.singleton str of λ where
      (T.non-strict , PE.refl) → _ , T.refl ,
        (T.lam (erase str u T.[ T.liftSubst (T.sgSubst T.↯) ]
                  T.[ T.liftSubst σ′ ])
           T.∘⟨ str ⟩ (erase str t T.[ σ′ ])                              ⇒⟨ T.β-red _ ⟩

         erase str u T.[ T.liftSubst (T.sgSubst T.↯) ]
           T.[ T.liftSubst σ′ ] T.[ erase str t T.[ σ′ ] ]₀               ≡⟨ [liftSubst-sgSubst][liftSubst][]₀≡ (erase _ u) ⟩⇒

         erase str u
           T.[ T.consSubst (T.consSubst σ′ T.↯) (erase str t T.[ σ′ ]) ]  ∎⇒)
      (T.strict , PE.refl) →
        case reduces-to-value [σGt₁] t₂®v₂ of λ
          (v₂′ , v₂′-val , v₂⇒*v₂′) →
        case TP.red*concat d′ v₂⇒*v₂′ of λ
          erase-t[σ′]⇒*v₂′ →
        _ , erase-t[σ′]⇒*v₂′ ,
        (T.lam (erase str u T.[ T.liftSubst (T.sgSubst T.↯) ]
                  T.[ T.liftSubst σ′ ])
           T.∘⟨ str ⟩ (erase str t T.[ σ′ ])                     ⇒*⟨ TP.app-subst*-arg T.lam erase-t[σ′]⇒*v₂′ ⟩

         T.lam (erase str u T.[ T.liftSubst (T.sgSubst T.↯) ]
                  T.[ T.liftSubst σ′ ])
           T.∘⟨ str ⟩ v₂′                                        ⇒⟨ T.β-red v₂′-val ⟩

         erase str u T.[ T.liftSubst (T.sgSubst T.↯) ]
           T.[ T.liftSubst σ′ ] T.[ v₂′ ]₀                       ≡⟨ [liftSubst-sgSubst][liftSubst][]₀≡ (erase _ u) ⟩⇒

         erase str u T.[ T.consSubst (T.consSubst σ′ T.↯) v₂′ ]  ∎⇒)
  σ®σ′ᵤ  = subsumptionSubst σ®σ′ λ x rγ+δ≡𝟘 →
             +-positiveʳ (PE.trans (PE.sym (lookup-distrib-+ᶜ (r ·ᶜ γ) δ x)) rγ+δ≡𝟘)
  t₁®v₁ = subsumptionTerm {p = p} t®v◂𝟘 λ _ → PE.trans (·-identityˡ (r · 𝟘)) (·-zeroʳ r)
  pr®pr′ =
    case red″ of λ
      (_ , erase-t⇒* , red″) →
    redSubstTerm* [σ₊A₊]
      (⊩ʳu [σ₊]
         ( (σ®σ′ᵤ , t₁®v₁)
         , (targetRedSubstTerm*′ [σGt₁]
              (targetRedSubstTerm* [σGt₁] t₂®v₂ d′)
              erase-t⇒* ◀ _)
         ) ◀≢𝟘 non-trivial)
      red′ red″

prodrecωʳ′-ω :
  {Γ : Con Term n}
  ([Γ] : ⊩ᵛ Γ)
  ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
  ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
  (ok : Σʷ-allowed p q) →
  Γ ∙ (Σʷ p , q ▷ F ▹ G) ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ Σᵛ [Γ] [F] [G] ok →
  ([A₊] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ A [ prodʷ p (var x1) (var x0) ]↑² /
            [Γ] ∙ [F] ∙ [G]) →
  δ ∙ (r · p) ∙ r ▸ Γ ∙ F ∙ G ⊩ʳ⟨ l ⟩ u ∷[ 𝟙ᵐ ]
    A [ prodʷ p (var x1) (var x0) ]↑² / [Γ] ∙ [F] ∙ [G] / [A₊] →
  ([At] : Γ ⊩ᵛ⟨ l ⟩ A [ t ]₀ / [Γ]) →
  Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ u ∷ A [ prodʷ p (var x1) (var x0) ]↑² /
    [Γ] ∙ [F] ∙ [G] / [A₊] →
  ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ) →
  σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ r ·ᶜ γ +ᶜ δ / [Γ] / [σ] →
  ([t₁] : Δ ⊩⟨ l ⟩ t₁ ∷ F [ σ ] / [F] .unwrap ⊢Δ [σ] .proj₁) →
  Δ ⊩⟨ l ⟩ t₂ ∷ G [ consSubst σ t₁ ] /
    [G] .unwrap ⊢Δ ([σ] , [t₁]) .proj₁ →
  Δ ⊢ t [ σ ] ⇒* prodʷ p t₁ t₂ ∷ Σʷ p , q ▷ F ▹ G [ σ ] →
  erase str t T.[ σ′ ] T.⇒* T.prod v₁ v₂ →
  t₁ ®⟨ l ⟩ v₁ ∷ F [ σ ] / [F] .unwrap ⊢Δ [σ] .proj₁ →
  t₂ ®⟨ l ⟩ v₂ ∷ G [ consSubst σ t₁ ] /
    [G] .unwrap ⊢Δ ([σ] , [t₁]) .proj₁ →
  p PE.≢ 𝟘 → r PE.≢ 𝟘 →
  prodrec r p q′ A t u [ σ ] ®⟨ l ⟩
    erase str (prodrec r p q′ A t u) T.[ σ′ ] ∷ A [ t ]₀ [ σ ] /
    [At] .unwrap ⊢Δ [σ] .proj₁
prodrecωʳ′-ω
  {F} {G} {p} {q} {A} {δ} {r} {u} {t} {σ} {σ′} {γ} {t₁} {t₂} {v₁} {v₂}
  {Γ} [Γ] [F] [G] ok [A] [A₊] ⊩ʳu [At] [u] [σ] σ®σ′ [t₁] [t₂] d d′
  t₁®v₁ t₂®v₂ p≢𝟘 r≢𝟘 with is-𝟘? r
... | yes r≡𝟘 = ⊥-elim (r≢𝟘 r≡𝟘)
... | no _ with is-𝟘? p
... | yes p≡𝟘 = ⊥-elim (p≢𝟘 p≡𝟘)
... | no _ =
  let σ®σ′ᵤ = subsumptionSubst σ®σ′ λ x rγ+δ≡𝟘 →
                +-positiveʳ (PE.trans (PE.sym (lookup-distrib-+ᶜ (r ·ᶜ γ) δ x)) rγ+δ≡𝟘)
      σ₊ = consSubst (consSubst σ t₁) t₂
      t₁®v₁′ = t₁®v₁ ◀ _
      t₂®v₂′ = t₂®v₂ ◀ _
      σ₊®σ′₊ = (σ®σ′ᵤ , t₁®v₁′) , t₂®v₂′
      [σ₊] = ([σ] , [t₁]) , [t₂]
      u®u′ = ⊩ʳu {σ = σ₊}
                 {σ′ = T.consSubst (T.consSubst σ′ v₁) v₂}
                 [σ₊] σ₊®σ′₊
      [σ₊A₊] = proj₁ (unwrap [A₊] {σ = σ₊} ⊢Δ [σ₊])

      [σF] = proj₁ (unwrap [F] ⊢Δ [σ])
      ⊢σF = escape [σF]
      [⇑σ] = liftSubstS {σ = σ} {F = F} [Γ] ⊢Δ [F] [σ]
      [σG] = proj₁ (unwrap [G] {σ = liftSubst σ} (⊢Δ ∙ ⊢σF) [⇑σ])
      ⊢σG = escape [σG]
      [σGt₁] = proj₁ (unwrap [G] ⊢Δ ([σ] , [t₁]))
      [Σ] = Σᵛ {F = F} {G} {q = q} {m = 𝕨} [Γ] [F] [G] _
      [σΣ] = proj₁ (unwrap [Σ] ⊢Δ [σ])
      ⊢σΣ = escape [σΣ]
      [σA] = [A] .unwrap {σ = liftSubst σ} (⊢Δ ∙ ⊢σΣ)
               (liftSubstS [Γ] ⊢Δ [Σ] [σ]) .proj₁
      ⊢σA = escape [σA]
      [σAt] = proj₁ (unwrap [At] ⊢Δ [σ])
      [⇑²σ] = liftSubstS {σ = liftSubst σ} {F = G} (_∙_ {A = F} [Γ] [F]) (⊢Δ ∙ ⊢σF) [G] [⇑σ]
      [σA₊] = proj₁ (unwrap [A₊] {σ = liftSubstn σ 2} (⊢Δ ∙ ⊢σF ∙ ⊢σG) [⇑²σ])
      [σu] = proj₁ ([u] {σ = liftSubstn σ 2} (⊢Δ ∙ ⊢σF ∙ ⊢σG) [⇑²σ])
      ⊢σu = escapeTerm [σA₊] [σu]
      ⊢σu′ = PE.subst (λ x → _ ⊢ u [ liftSubstn σ 2 ] ∷ x) (subst-β-prodrec A σ) ⊢σu
      ⊢t₁ = escapeTerm [σF] [t₁]
      ⊢t₂ = escapeTerm [σGt₁] [t₂]
      ⊢t₂′ = PE.subst (λ x → Δ ⊢ t₂ ∷ x) (PE.sym (singleSubstComp t₁ σ G)) ⊢t₂

      red₁ = prodrec-subst* {r = r} d ⊢σF ⊢σG ⊢σA ⊢σu′
      red₂ = prodrec-β ⊢σF ⊢σG ⊢σA ⊢t₁ ⊢t₂′ ⊢σu′ PE.refl ok
      At≡Ap = substTypeEq (refl ⊢σA) (subset*Term d)
      red = PE.subst₂ (λ x y → Δ ⊢ _ ⇒* x ∷ y)
                      (doubleSubstComp u t₁ t₂ σ)
                      (substCompProdrec A t₁ t₂ σ)
                      (conv* red₁ At≡Ap ⇨∷* redMany red₂)

      red′₁ = TP.prodrec-subst* d′
      red′₂ = PE.subst (T._⇒_ _)
                (TP.doubleSubstComp (erase _ u) _ _ _)
                T.prodrec-β
      red′ = TP.red*concat red′₁ (T.trans red′₂ T.refl)

      pr®pr′ = redSubstTerm* [σ₊A₊] (u®u′ ◀≢𝟘 non-trivial) red red′
      At≡Ap′ = PE.subst₂ (λ x y → Δ ⊢ x ≡ y)
                         (PE.sym (singleSubstLift A t))
                         (substCompProdrec A t₁ t₂ σ)
                         At≡Ap
  in  convTermʳ [σ₊A₊] [σAt] (sym At≡Ap′) pr®pr′

prodrecωʳ′ :
  {Γ : Con Term n}
  ([Γ] : ⊩ᵛ Γ)
  ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
  ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
  (ok : Σʷ-allowed p q) →
  let [Σ] = Σᵛ [Γ] [F] [G] ok in
  Γ ∙ (Σʷ p , q ▷ F ▹ G) ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ [Σ] →
  ([A₊] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ A [ prodʷ p (var x1) (var x0) ]↑² /
            [Γ] ∙ [F] ∙ [G]) →
  δ ∙ (r · p) ∙ r ▸ Γ ∙ F ∙ G ⊩ʳ⟨ l ⟩ u ∷[ 𝟙ᵐ ]
    A [ prodʷ p (var x1) (var x0) ]↑² / [Γ] ∙ [F] ∙ [G] / [A₊] →
  ([At] : Γ ⊩ᵛ⟨ l ⟩ A [ t ]₀ / [Γ]) →
  Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ u ∷ A [ prodʷ p (var x1) (var x0) ]↑² /
    [Γ] ∙ [F] ∙ [G] / [A₊] →
  r PE.≢ 𝟘 →
  ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ) →
  σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ r ·ᶜ γ +ᶜ δ / [Γ] / [σ] →
  Δ ⊩⟨ l ⟩ t [ σ ] ∷ Σʷ p , q ▷ F ▹ G [ σ ] /
    [Σ] .unwrap ⊢Δ [σ] .proj₁ →
  t [ σ ] ®⟨ l ⟩ erase str t T.[ σ′ ] ∷ Σʷ p , q ▷ F ▹ G [ σ ] /
    [Σ] .unwrap ⊢Δ [σ] .proj₁ →
  prodrec r p q′ A t u [ σ ] ®⟨ l ⟩
    erase str (prodrec r p q′ A t u) T.[ σ′ ] ∷
    A [ t ]₀ [ σ ] / [At] .unwrap ⊢Δ [σ] .proj₁
prodrecωʳ′
  {n = n} {l = l} {F = F} {G = G} {p = p′} {q = q} {A = A} {δ = δ} {r = r} {u = u}
  {t = t} {σ = σ} {σ′ = σ′} {γ = γ} {q′ = q′} {Γ = Γ}
  [Γ] [F] [G] ok [A] [A₊] ⊩ʳu [At] [u] r≢𝟘 [σ] σ®σ′
  (Σₜ p t⇒p p≅p prodₙ (foo , [t₁] , [t₂] , PE.refl))
  (t₁ , t₂ , d , [t₁]₁ , v₂ , t₂®v₂ , extra)
  with is-𝟘? r
... | yes r≡𝟘 = ⊥-elim (r≢𝟘 r≡𝟘)
... | no _
  with whrDet*Term (redₜ t⇒p , prodₙ) (d , prodₙ)
... | PE.refl = PE.subst (λ x → prodrec r p′ q′ A t u [ σ ] ®⟨ l ⟩ x ∷ A [ t ]₀ [ σ ] / [At] .unwrap ⊢Δ [σ] .proj₁)
                         (PE.cong (T._[ σ′ ]) (prodrec-ω {q = q′} {A = A} p′ r≢𝟘))
                         pr®pr′
  where
  [σF] = proj₁ (unwrap [F] ⊢Δ [σ])
  ⊢σF = escape [σF]
  [σF]′ = W.wk id ⊢Δ [σF]
  [σF]″ = W.wk id (wf ⊢σF) [σF]
  [t₁]′ = I.irrelevanceTerm′ (wk-id (F [ σ ])) [σF]″ [σF] [t₁]
  [Gt₁] = proj₁ (unwrap [G] {σ = consSubst σ t₁} ⊢Δ
                            ([σ] , [t₁]′))
  [idσ] = wkSubstS [Γ] ⊢Δ (wf ⊢σF) id [σ]
  [σF]‴ = proj₁ (unwrap [F] (wf ⊢σF) [idσ])
  [t₁]″ = I.irrelevanceTerm′ (wk-subst F) [σF]″ [σF]‴ [t₁]
  [Gt₁]′ = proj₁ (unwrap [G] {σ = consSubst (id •ₛ σ) t₁} (wf ⊢σF) ([idσ] , [t₁]″))
  [Gt₁]″ = I.irrelevance′ (PE.sym (PE.trans (PE.cong (_[ t₁ ]₀) (wk-subst-lift G))
                                            (singleSubstComp t₁ (id •ₛ σ) G)))
                          [Gt₁]′
  [t₂]′ = I.irrelevanceTerm′ (PE.trans (PE.cong (_[ t₁ ]₀) (wk-lift-id (G [ liftSubst σ ])))
                                       (singleSubstComp t₁ σ G))
                             [Gt₁]″ [Gt₁] [t₂]
  [idσ]′ = wkSubstS [Γ] ⊢Δ ⊢Δ id [σ]
  [σF]₁ = proj₁ (unwrap [F] ⊢Δ [idσ]′)
  [t₁]₁′ = I.irrelevanceTerm′ (wk-subst F) [σF]′ [σF]₁ [t₁]₁
  [Gt₁]₁ = proj₁ (unwrap [G] {σ = consSubst (id •ₛ σ) t₁} ⊢Δ ([idσ]′ , [t₁]₁′))
  [Gt₁]₁′ = I.irrelevance′ (PE.sym (PE.trans (PE.cong (_[ t₁ ]₀) (wk-subst-lift G))
                                             (singleSubstComp t₁ (id •ₛ σ) G)))
                           [Gt₁]₁
  t₂®v₂′ = irrelevanceTerm′ (PE.trans (PE.cong (_[ t₁ ]₀) (wk-lift-id (G [ liftSubst σ ])))
                                      (singleSubstComp t₁ σ G))
                            [Gt₁]₁′ [Gt₁] t₂®v₂
  pr = prodrec r p′ q′ A t u
  [σAt] = proj₁ (unwrap [At] ⊢Δ [σ])
  pr®pr′ =
    Σ-®-elim
      (λ _ →
         pr [ σ ] ®⟨ l ⟩ erase str pr T.[ σ′ ] ∷ A [ t ]₀ [ σ ] / [σAt])
      extra
      (λ d′ p≡𝟘 →
        prodrecωʳ′-𝟘 {δ = δ} {u = u} {γ = γ} {q′ = q′}
          [Γ] [F] [G] ok [A] [A₊] ⊩ʳu [At] [u] [σ] σ®σ′
          [t₁]′ [t₂]′ d d′ t₂®v₂′ p≡𝟘 r≢𝟘)
      (λ v₁ d′ t₁®v₁ p≢𝟘 →
        let t₁®v₁′ = irrelevanceTerm′ (wk-id (F [ σ ]))
                       [σF]′ [σF] t₁®v₁
        in  prodrecωʳ′-ω {δ = δ} {u = u} {γ = γ} {q′ = q′}
              [Γ] [F] [G] ok [A] [A₊] ⊩ʳu [At] [u] [σ] σ®σ′
              [t₁]′ [t₂]′ d d′ t₁®v₁′ t₂®v₂′ p≢𝟘 r≢𝟘)

prodrecωʳ′ _ _ _ _ _ _ _ _ _ _ _ _ (Σₜ _ t⇒p _ (ne x) _) (_ , _ , d , _)
  with whrDet*Term (redₜ t⇒p , ne x) (d , prodₙ) | x
... | PE.refl | ()

prodrec𝟘ʳ :
  {Γ : Con Term n}
  ([Γ] : ⊩ᵛ Γ)
  ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
  ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
  (ok : Σʷ-allowed p q) →
  let [Σ] = Σᵛ [Γ] [F] [G] ok in
  Γ ∙ (Σʷ p , q ▷ F ▹ G) ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ [Σ] →
  ([A₊] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ A [ prodʷ p (var x1) (var x0) ]↑² /
            [Γ] ∙ [F] ∙ [G]) →
  δ ∙ 𝟘 ∙ 𝟘 ▸ Γ ∙ F ∙ G ⊩ʳ⟨ l ⟩ u ∷[ 𝟙ᵐ ]
    A [ prodʷ p (var x1) (var x0) ]↑² / [Γ] ∙ [F] ∙ [G] / [A₊] →
  ([At] : Γ ⊩ᵛ⟨ l ⟩ A [ t ]₀ / [Γ]) →
  Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ u ∷ A [ prodʷ p (var x1) (var x0) ]↑² /
    [Γ] ∙ [F] ∙ [G] / [A₊] →
  r PE.≡ 𝟘 →
  k PE.≡ 0 →
  ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ) →
  σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ δ / [Γ] / [σ] →
  Δ ⊩⟨ l ⟩ t [ σ ] ∷ Σʷ p , q ▷ F ▹ G [ σ ] /
    [Σ] .unwrap ⊢Δ [σ] .proj₁ →
  prodrec r p q′ A t u [ σ ] ®⟨ l ⟩
    erase str (prodrec r p q′ A t u) T.[ σ′ ] ∷
    A [ t ]₀ [ σ ] / [At] .unwrap ⊢Δ [σ] .proj₁
prodrec𝟘ʳ {n} {l} {F} {G} {p} {q} {A} {δ} {u} {t} {r} {σ} {σ′} {q′} {Γ}
          [Γ] [F] [G] ok [A] [A₊] ⊩ʳu [At] [u] r≡𝟘 PE.refl [σ] σ®σ′
          (Σₜ t′ t⇒t′ p≅p (prodₙ {t = t₁} {u = t₂})
             (PE.refl , [t₁]′ , [t₂]′ , PE.refl))
          with is-𝟘? r
... | yes _ =
  let [Σ] = Σᵛ [Γ] [F] [G] _
      [σF] = proj₁ (unwrap [F] ⊢Δ [σ])
      ⊢σF = escape [σF]
      [⇑σ] = liftSubstS [Γ] ⊢Δ [F] [σ]
      [σG] = proj₁ (unwrap [G] {σ = liftSubst σ} (⊢Δ ∙ ⊢σF) [⇑σ])
      ⊢σG = escape [σG]
      [σΣ] = proj₁ (unwrap [Σ] ⊢Δ [σ])
      ⊢σΣ = escape [σΣ]
      [⇑σ]′ = liftSubstS [Γ] ⊢Δ [Σ] [σ]
      [σA] = proj₁ (unwrap [A] {σ = liftSubst σ} (⊢Δ ∙ ⊢σΣ) [⇑σ]′)
      ⊢σA = escape [σA]
      [⇑²σ] = liftSubstS ([Γ] ∙ [F]) (⊢Δ ∙ ⊢σF) [G] [⇑σ]
      [σA₊] = proj₁ (unwrap [A₊] {σ = liftSubstn σ 2} (⊢Δ ∙ ⊢σF ∙ ⊢σG) [⇑²σ])
      [σu] = proj₁ ([u] {σ = liftSubstn σ 2} (⊢Δ ∙ ⊢σF ∙ ⊢σG) [⇑²σ])
      ⊢σu = escapeTerm [σA₊] [σu]
      ⊢σu′ = PE.subst (λ x → _ ⊢ u [ liftSubstn σ 2 ] ∷ x)
                      (subst-β-prodrec A σ) ⊢σu

      ⊢Δ′ = wf ⊢σF
      [σF]′ = W.wk id ⊢Δ′ [σF]
      [t₁] = I.irrelevanceTerm′ (wk-id (F [ σ ])) [σF]′ [σF] [t₁]′
      ⊢t₁ = escapeTerm [σF] [t₁]
      [Gt₁] = proj₁ (unwrap [G] ⊢Δ ([σ] , [t₁]))
      [σ]′ = wkSubstS [Γ] ⊢Δ ⊢Δ′ id [σ]
      [σF]″ = proj₁ (unwrap [F] ⊢Δ′ [σ]′)
      [t₁]″ = I.irrelevanceTerm′ (wk-subst F) [σF]′ [σF]″ [t₁]′
      [Gt₁]″ = proj₁ (unwrap [G] ⊢Δ′ ([σ]′ , [t₁]″))
      [Gt₁]′ = I.irrelevance′ (PE.sym (PE.trans (PE.cong (_[ t₁ ]₀) (wk-subst-lift G))
                                                (singleSubstComp _ _ G)))
                              [Gt₁]″
      [t₂] = I.irrelevanceTerm′ (PE.trans (PE.cong (_[ t₁ ]₀) (wk-lift-id (G [ liftSubst σ ])))
                                          (PE.trans (substCompEq G) (substSingletonComp G)))
                                [Gt₁]′ [Gt₁] [t₂]′
      ⊢t₂ = escapeTerm [Gt₁] [t₂]
      ⊢t₂′ = PE.subst (λ x → _ ⊢ t₂ ∷ x)
                      (PE.sym (singleSubstComp t₁ σ G)) ⊢t₂

      σ₊ = consSubst (consSubst σ t₁) t₂
      σ′₊ = T.consSubst (T.consSubst σ′ T.↯) T.↯
      [σ₊] = ([σ] , [t₁]) , [t₂]
      σ₊®σ′₊ = (σ®σ′ , PE.subst (λ p → t₁ ®⟨ l ⟩ T.↯ ∷ F [ σ ] ◂ p / [σF])
                                (PE.sym (·-zeroʳ 𝟙)) t®v◂𝟘)
                    , PE.subst (λ p → t₂ ®⟨ _ ⟩ T.↯ ∷ G [ consSubst σ t₁ ] ◂ p / [Gt₁])
                               (PE.sym (·-zeroʳ 𝟙)) t®v◂𝟘
      σ₊u®σ′₊u′ = ⊩ʳu {σ = σ₊} {σ′ = σ′₊} [σ₊] σ₊®σ′₊
      [σ₊A₊] = proj₁ (unwrap [A₊] {σ = σ₊} ⊢Δ [σ₊])

      At≡At′ = substTypeEq (refl ⊢σA) (subset*Term (redₜ t⇒t′))
      At≡At″ = PE.subst (λ x → Δ ⊢ _ ≡ x) (substCompProdrec A t₁ t₂ σ) At≡At′

      red₁ = prodrec-subst* (redₜ t⇒t′) ⊢σF ⊢σG ⊢σA ⊢σu′
      red₁′ = conv* red₁ At≡At″
      red₂ = redMany $
             prodrec-β ⊢σF ⊢σG ⊢σA ⊢t₁ ⊢t₂′ ⊢σu′ PE.refl ok
      red₂′ = PE.subst (λ x → _ ⊢ prodrec r p q′ _ _ _ ⇒* _ ∷ x) (substCompProdrec A t₁ t₂ σ) red₂
      red = PE.subst (λ x → _ ⊢ prodrec r p q′ A t u [ σ ] ⇒* x ∷ _)
                     (doubleSubstComp u t₁ t₂ σ)
                     (red₁′ ⇨∷* red₂′)
      red′ = PE.subst (T._⇒*_ _)
               (TP.doubleSubstComp′ (erase _ u))
               T.refl


      pr®pr′ = redSubstTerm* [σ₊A₊] (σ₊u®σ′₊u′ ◀≢𝟘 non-trivial)
                             red red′
      [σAt] = proj₁ (unwrap [At] ⊢Δ [σ])
      At≡At‴ = PE.subst (λ x → Δ ⊢ x ≡ _) (PE.sym (singleSubstLift A t)) At≡At″

  in  convTermʳ [σ₊A₊] [σAt] (sym At≡At‴) pr®pr′

... | no r≢𝟘 = ⊥-elim (r≢𝟘 r≡𝟘)
prodrec𝟘ʳ {n} {l} {F} {G} {p} {q} {A} {δ} {u} {t} {r} {σ} {σ′} {q′} {Γ}
          [Γ] [F] [G] _ x [A₊] x₁ [At] x₂ r≡𝟘 PE.refl [σ] x₄
          (Σₜ t′ t⇒t′ p≅p (ne y) prop) = ⊥-elim (noClosedNe y)

prodrecʳ :
  ([Γ] : ⊩ᵛ Γ)
  ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
  ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
  ([Σ] : Γ ⊩ᵛ⟨ l ⟩ Σʷ p , q ▷ F ▹ G / [Γ]) →
  Γ ∙ (Σʷ p , q ▷ F ▹ G) ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ [Σ] →
  ([A₊] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ A [ prodʷ p (var x1) (var x0) ]↑² /
            [Γ] ∙ [F] ∙ [G]) →
  Γ ⊩ᵛ⟨ l ⟩ t ∷ Σʷ p , q ▷ F ▹ G / [Γ] / [Σ] →
  Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ u ∷ A [ prodʷ p (var x1) (var x0) ]↑² /
    [Γ] ∙ [F] ∙ [G] / [A₊] →
  (r PE.≢ 𝟘 → γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ] Σʷ p , q ▷ F ▹ G / [Γ] / [Σ]) →
  δ ∙ (⌜ m ⌝ · r · p) ∙ (⌜ m ⌝ · r) ▸ Γ ∙ F ∙ G ⊩ʳ⟨ l ⟩ u ∷[ m ]
    A [ prodʷ p (var x1) (var x0) ]↑² / [Γ] ∙ [F] ∙ [G] / [A₊] →
  (r PE.≡ 𝟘 → k PE.≡ 0) →
  ∃ λ ([At] : Γ ⊩ᵛ⟨ l ⟩ A [ t ]₀ / [Γ]) →
    r ·ᶜ γ +ᶜ δ ▸ Γ ⊩ʳ⟨ l ⟩ prodrec r p q′ A t u ∷[ m ] A [ t ]₀ / [Γ] /
      [At]
prodrecʳ {m = 𝟘ᵐ} [Γ] [F] [G] [Σ] [A] [A₊] [t] [u] ⊩ʳt ⊩ʳu r≢𝟘
  with is-𝟘? 𝟘
... | yes _  = substS [Γ] [Σ] [A] [t] , _
... | no 𝟘≢𝟘 = ⊥-elim (𝟘≢𝟘 PE.refl)
prodrecʳ
  {Γ = Γ} {l = l} {p = p} {t = t} {u = u} {r = r} {γ = γ} {m = 𝟙ᵐ} {δ = δ}
  [Γ] [F] [G] [Σ] [A] [A₊] [t] [u] ⊩ʳt ⊩ʳu r≡𝟘→k≡0
  with is-𝟘? 𝟙
... | yes 𝟙≡𝟘 = ⊥-elim (non-trivial 𝟙≡𝟘)
... | no 1≢𝟘 =
  let [At] = substS [Γ] [Σ] [A] [t]
  in  [At] , λ {σ} [σ] σ®σ′ →
    let ok = ⊩ᵛΠΣ→ΠΣ-allowed [Σ]
        [Σ]′ = Σᵛ [Γ] [F] [G] ok
        [A]′ = IS.irrelevance ([Γ] ∙ [Σ]) ([Γ] ∙ [Σ]′) [A]
        [t]′ = IS.irrelevanceTerm {t = t} [Γ] [Γ] [Σ] [Σ]′ [t]
        [σt] = proj₁ ([t]′ ⊢Δ [σ])
        ⊩ʳu′ = subsumption {t = u} ([Γ] ∙ [F] ∙ [G]) [A₊]
                           (subsumption′ {t = u} ([Γ] ∙ [F] ∙ [G]) [A₊] ⊩ʳu)
                           lemma′
    in case is-𝟘? r of λ where
      (yes r≡𝟘) →
        let ⊩ʳu″ = PE.subst (λ x → x ▸ _ ∙ _ ∙ _ ⊩ʳ⟨ l ⟩ u ∷[ 𝟙ᵐ ] _ / [Γ] ∙ [F] ∙ [G] / [A₊])
                            (PE.cong₃ (λ x y z → (x ∙ y) ∙ z)
                                      (PE.sym (PE.trans (PE.cong (λ x → x ·ᶜ γ +ᶜ δ) r≡𝟘)
                                              (≈ᶜ→≡ (≈ᶜ-trans (+ᶜ-congʳ (·ᶜ-zeroˡ γ))
                                                              (+ᶜ-identityˡ δ)))))
                                      (PE.trans (·-congʳ r≡𝟘) (·-zeroˡ p))
                                      r≡𝟘)
                            ⊩ʳu′
        in  prodrec𝟘ʳ [Γ] [F] [G] ok [A]′ [A₊] ⊩ʳu″ [At] [u]
              r≡𝟘 (r≡𝟘→k≡0 r≡𝟘) [σ] σ®σ′ [σt]
      (no r≢𝟘) →
        let ⊩ʳt′ = irrelevance {t = t} [Γ] [Γ] [Σ] [Σ]′ (subsumption′ {t = t} [Γ] [Σ] (⊩ʳt r≢𝟘))
            t®t′ = ⊩ʳt′ [σ] (subsumptionSubst σ®σ′ (lemma r≢𝟘))
        in  prodrecωʳ′ [Γ] [F] [G] ok [A]′ [A₊] ⊩ʳu′ [At] [u]
              r≢𝟘 [σ] σ®σ′ [σt] (t®t′ ◀≢𝟘 non-trivial)
    where
    lemma : (r PE.≢ 𝟘) → (x : Fin _) → (r ·ᶜ γ +ᶜ δ) ⟨ x ⟩ PE.≡ 𝟘 → γ ⟨ x ⟩ PE.≡ 𝟘
    lemma r≢𝟘 x rγ+δ≡𝟘 =
      case zero-product (PE.trans (PE.sym (lookup-distrib-·ᶜ γ r x))
                        (+-positiveˡ (PE.trans (PE.sym (lookup-distrib-+ᶜ (r ·ᶜ γ) δ x))
                                             rγ+δ≡𝟘))) of λ where
        (inj₁ r≡𝟘) → ⊥-elim (r≢𝟘 r≡𝟘)
        (inj₂ γx≡𝟘) → γx≡𝟘
    lemma′ : ∀ x → (δ ∙ (r · p) ∙ r) ⟨ x ⟩ PE.≡ 𝟘 → (δ ∙ (𝟙 · r · p) ∙ (𝟙 · r)) ⟨ x ⟩ PE.≡ 𝟘
    lemma′ x0 r≡𝟘 = PE.trans (·-identityˡ r) r≡𝟘
    lemma′ (x0 +1) rp≡𝟘 = PE.trans (·-identityˡ (r · p)) rp≡𝟘
    lemma′ (x +2) δx≡𝟘 = δx≡𝟘
