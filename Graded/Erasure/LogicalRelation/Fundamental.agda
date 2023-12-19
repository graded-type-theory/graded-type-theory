------------------------------------------------------------------------
-- The fundamental lemma of the logical relation.
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.EqualityRelation
import Definition.Typed
open import Definition.Typed.Restrictions
import Definition.Untyped hiding (_∷_)
open import Tools.Empty
open import Tools.Sum hiding (id)
import Tools.PropositionalEquality as PE

module Graded.Erasure.LogicalRelation.Fundamental
  {a} {M : Set a}
  {𝕄 : Modality M}
  (open Modality 𝕄)
  (TR : Type-restrictions 𝕄)
  (UR : Usage-restrictions M)
  ⦃ 𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet ⦄
  {{eqrel : EqRelSet TR}}
  where

open Definition.Untyped M
open Definition.Typed TR
open EqRelSet {{...}}

open import Definition.LogicalRelation TR
open import Definition.LogicalRelation.Properties.Escape TR
open import Definition.LogicalRelation.Substitution TR
open import Definition.LogicalRelation.Substitution.MaybeEmbed TR
open import Definition.LogicalRelation.Substitution.Properties TR
open import Definition.LogicalRelation.Substitution.Weakening TR
open import
  Definition.LogicalRelation.Substitution.Introductions.Identity TR
open import Definition.LogicalRelation.Substitution.Introductions.DoubleSubst TR
open import Definition.LogicalRelation.Substitution.Introductions.Pi TR
open import Definition.LogicalRelation.Substitution.Introductions.Nat TR
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst TR
import Definition.LogicalRelation.Substitution.Introductions.Var TR as V

import Definition.LogicalRelation.Fundamental TR as F
import Definition.LogicalRelation.Irrelevance TR as I
import Definition.LogicalRelation.Substitution.Irrelevance TR as IS

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Modality.Dedicated-nr.Instance
open import Graded.Modality.Nr-instances
open import Graded.Modality.Properties 𝕄
open import Graded.Usage 𝕄 UR
open import Graded.Usage.Inversion 𝕄 UR
open import Graded.Usage.Properties 𝕄 UR
open import Graded.Mode 𝕄

open import Definition.Untyped.Properties M
open import Definition.Typed.Consequences.Syntactic TR

import Graded.Erasure.LogicalRelation TR is-𝟘? as LR
open import Graded.Erasure.LogicalRelation.Fundamental.Assumptions TR UR
import Graded.Erasure.LogicalRelation.Fundamental.Application
import Graded.Erasure.LogicalRelation.Fundamental.Empty
import Graded.Erasure.LogicalRelation.Fundamental.Identity
import Graded.Erasure.LogicalRelation.Fundamental.Lambda
import Graded.Erasure.LogicalRelation.Fundamental.Nat
import Graded.Erasure.LogicalRelation.Fundamental.Natrec
import Graded.Erasure.LogicalRelation.Fundamental.Prodrec
import Graded.Erasure.LogicalRelation.Fundamental.Product
import Graded.Erasure.LogicalRelation.Fundamental.Unit
import Graded.Erasure.LogicalRelation.Conversion
import Graded.Erasure.LogicalRelation.Hidden
import Graded.Erasure.LogicalRelation.Irrelevance
import Graded.Erasure.LogicalRelation.Subsumption

import Graded.Erasure.Target as T
open import Graded.Erasure.Extraction 𝕄 is-𝟘?
import Graded.Erasure.Target.Properties as TP

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PartialOrder
open import Tools.Relation
import Tools.PropositionalEquality as PE

private
  variable
     l n : Nat
     Γ Δ : Con Term n
     t u A B : Term n
     γ δ : Conₘ n
     p q : M
     σ : Subst l n
     x : Fin n
     σ′ : T.Subst l n
     m : Mode
     ⊩Γ : ⊩ᵛ _

-- Some lemmas.

module _ (⊢Δ : ⊢ Δ) where

  open LR ⊢Δ

  open Graded.Erasure.LogicalRelation.Conversion TR is-𝟘? ⊢Δ
  open Graded.Erasure.LogicalRelation.Irrelevance TR is-𝟘? ⊢Δ
  open Graded.Erasure.LogicalRelation.Subsumption TR is-𝟘? ⊢Δ

  -- A special case of subsumption.

  subsumption-≤ : ∀ {l}
                → ([Γ] : ⊩ᵛ Γ) ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
                → γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ] A / [Γ] / [A]
                → δ ≤ᶜ γ
                → δ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ] A / [Γ] / [A]
  subsumption-≤ {t = t} [Γ] [A] γ⊩ʳt δ≤γ =
    subsumption {t = t} [Γ] [A] γ⊩ʳt λ x δx≡𝟘 → lemma x δx≡𝟘 δ≤γ
    where
    lemma : (x : Fin n) → δ ⟨ x ⟩ PE.≡ 𝟘 → δ ≤ᶜ γ
          → γ ⟨ x ⟩ PE.≡ 𝟘
    lemma {δ = δ ∙ p} {γ ∙ q} x0 PE.refl (δ≤γ ∙ p≤q) = 𝟘≮ p≤q
    lemma {δ = δ ∙ p} {γ ∙ q} (x +1) δx≡𝟘 (δ≤γ ∙ _) = lemma x δx≡𝟘 δ≤γ

  -- A lemma used to prove fundamentalVar.

  fundamentalVar′ :
    ([Γ] : ⊩ᵛ Γ) →
    x ∷ A ∈ Γ →
    γ ≤ᶜ 𝟘ᶜ , x ≔ 𝟙 →
    ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ) →
    (σ®σ′ : σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ γ / [Γ] / [σ]) →
    ∃ λ ([A] : Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ]) →
      σ x ®⟨ ¹ ⟩ σ′ x ∷ A [ σ ] / proj₁ (unwrap [A] ⊢Δ [σ])
  fundamentalVar′ ε ()
  fundamentalVar′ {σ = σ} (_∙_ {A = A} [Γ] [A]) here (_ ∙ p≤𝟙)
                  ([tailσ] , [headσ]) (σ®σ′ , σ0®σ′0) =
    let [A]′ = proj₁ (unwrap [A] ⊢Δ [tailσ])
        [↑A] = wk1ᵛ {A = A} {F = A} [Γ] [A] [A]
        [↑A]′ = maybeEmbᵛ {A = wk1 A} (_∙_ {A = A} [Γ] [A]) [↑A]
        [σ↑A] = proj₁ (unwrap [↑A]′ {σ = σ} ⊢Δ ([tailσ] , [headσ]))
        A≡A : Δ ⊢ A [ tail σ ] ≡ A [ tail σ ]
        A≡A = refl (escape [A]′)
        A≡A′ = PE.subst (Δ ⊢ A [ tail σ ] ≡_)
                        (PE.sym (wk1-tail A)) A≡A
        σ0®σ′0′ = σ0®σ′0 ◀≢𝟘 λ 𝟙p≡𝟘 →
          𝟘≰𝟙 $
          ≤-trans (≤-reflexive (PE.trans (PE.sym 𝟙p≡𝟘) (·-identityˡ _)))
            p≤𝟙
    in  [↑A]′ , convTermʳ [A]′ [σ↑A] A≡A′ σ0®σ′0′
  fundamentalVar′ (_∙_ {A = A} [Γ] [A]) (there {A = B} x) (γ≤eᵢ ∙ _)
                  ([tailσ] , [headσ]) (σ®σ′ , σ0®σ′0) =
    let [σA] = proj₁ (unwrap [A] ⊢Δ [tailσ])
        [A]′ = maybeEmbᵛ {A = A} [Γ] [A]
        [B] , t®v = fundamentalVar′ [Γ] x γ≤eᵢ [tailσ] σ®σ′
        [↑B] = wk1ᵛ {A = B} {F = A} [Γ] [A]′ [B]
        [↑B]′ = maybeEmbᵛ {A = wk1 B} (_∙_ {A = A} [Γ] [A]′) [↑B]
        [↑B]″ = IS.irrelevance {A = wk1 B} (_∙_ {A = A} [Γ] [A]′) ([Γ] ∙ [A]) [↑B]′
        t®v′ = irrelevanceTerm′ (PE.sym (wk1-tail B)) (proj₁ (unwrap [B] ⊢Δ [tailσ]))
                                (proj₁ (unwrap [↑B]″ ⊢Δ ([tailσ] , [headσ]))) t®v
    in  [↑B]″ , t®v′

  -- A fundamental lemma for variables.

  fundamentalVar : ([Γ] : ⊩ᵛ Γ)
                 → x ∷ A ∈ Γ
                 → γ ▸[ m ] var x
                 → ∃ λ ([A] : Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ])
                 → γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ var x ∷[ m ] A / [Γ] / [A]
  fundamentalVar {Γ = Γ} {x = x} {A = A} {γ = γ} {m = m} [Γ] x∷A∈Γ γ▸x =
    [A] , lemma m γ▸x
    where
    [A] = proj₁ (F.fundamentalVar x∷A∈Γ [Γ])

    lemma :
      ∀ m →
      γ ▸[ m ] var x →
      γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ var x ∷[ m ] A / [Γ] / [A]
    lemma 𝟘ᵐ with is-𝟘? 𝟘
    ... | yes 𝟘≡𝟘 = _
    ... | no 𝟘≢𝟘 = ⊥-elim (𝟘≢𝟘 PE.refl)

    lemma 𝟙ᵐ γ▸x [σ] σ®σ′ with is-𝟘? 𝟙
    ... | yes 𝟙≡𝟘 = ⊥-elim (non-trivial 𝟙≡𝟘)
    ... | no 𝟙≢𝟘 =
       let [A]′ , t®v =
             fundamentalVar′ [Γ] x∷A∈Γ (inv-usage-var γ▸x) [σ] σ®σ′
       in  irrelevanceTerm (proj₁ (unwrap [A]′ ⊢Δ [σ]))
             (proj₁ (unwrap [A] ⊢Δ [σ])) t®v

-- The fundamental lemma, and a variant for terms in fully erased
-- contexts.

module Fundamental (FA : Fundamental-assumptions Δ) where

  open Fundamental-assumptions FA

  open Graded.Erasure.LogicalRelation.Fundamental.Application
    TR well-formed
  open Graded.Erasure.LogicalRelation.Fundamental.Empty
    TR is-𝟘? well-formed consistent
  open Graded.Erasure.LogicalRelation.Fundamental.Identity
    TR well-formed
  open Graded.Erasure.LogicalRelation.Fundamental.Lambda
    TR is-𝟘? non-trivial well-formed
  open Graded.Erasure.LogicalRelation.Fundamental.Nat
    TR is-𝟘? well-formed
  open Graded.Erasure.LogicalRelation.Fundamental.Natrec
    TR well-formed
  open Graded.Erasure.LogicalRelation.Fundamental.Prodrec
    TR well-formed
  open Graded.Erasure.LogicalRelation.Fundamental.Product
    TR UR well-formed
  open Graded.Erasure.LogicalRelation.Fundamental.Unit
    TR well-formed
  open Graded.Erasure.LogicalRelation.Conversion TR is-𝟘? well-formed
  open Graded.Erasure.LogicalRelation.Hidden TR is-𝟘? well-formed
  open Graded.Erasure.LogicalRelation.Irrelevance TR is-𝟘? well-formed
  open Graded.Erasure.LogicalRelation.Subsumption TR is-𝟘? well-formed

  open LR well-formed

  -- The fundamental lemma for the erasure relation.
  --
  -- Note the assumptions of the local module Fundamental.
  --
  -- The main parts of this proof are located in Graded.Erasure.LogicalRelation.Fundamental.X
  -- The general proof strategy of these is the following:
  -- To show that t is valid, find t′ in whnf such that t ⇒* t′ and show that t′ is valid.
  -- The result that t is valid then follows from the logical relation being closed under
  -- reduction (see Graded.Erasure.LogicalRelation.Reduction).

  fundamental :
    Γ ⊢ t ∷ A → γ ▸[ m ] t →
    ∃₂ λ ([Γ] : ⊩ᵛ Γ) ([A] : Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ]) →
      γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ t ∷[ m ] A / [Γ] / [A]

  -- A variant of fundamental.

  fundamental′ :
    Γ ⊢ t ∷ A → γ ▸[ m ] t →
    ∃ λ (⊩A : Γ ⊩ᵛ⟨ ¹ ⟩ A / ⊩Γ) →
      γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ t ∷[ m ] A / ⊩Γ / ⊩A
  fundamental′ {t} ⊢t ▸t =
    case fundamental ⊢t ▸t of λ {
      (_ , ⊩A′ , ⊩ʳt) →
    case IS.irrelevance _ _ ⊩A′ of λ {
      ⊩A →
      ⊩A
    , λ {_ _} → irrelevance {t = t} _ _ ⊩A′ ⊩A ⊩ʳt }}

  -- Another variant of fundamental.

  fundamental″ :
    (⊩A : Γ ⊩ᵛ⟨ ¹ ⟩ A / ⊩Γ) →
    Γ ⊢ t ∷ A → γ ▸[ m ] t →
    γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ t ∷[ m ] A / ⊩Γ / ⊩A
  fundamental″ {t} ⊩A ⊢t ▸t =
    case fundamental ⊢t ▸t of λ {
      (_ , ⊩A′ , ⊩ʳt) →
    irrelevance {t = t} _ _ ⊩A′ ⊩A ⊩ʳt }

  fundamental {m = 𝟘ᵐ} ⊢t _ with is-𝟘? 𝟘
  ... | yes 𝟘≡𝟘 =
    case F.fundamental (syntacticTerm ⊢t) of λ ([Γ] , [A]) →
      [Γ] , [A] , _
  ... | no 𝟘≢𝟘 = ⊥-elim (𝟘≢𝟘 PE.refl)
  fundamental Γ⊢ΠΣ@(ΠΣⱼ Γ⊢F:U _ _) γ▸t =
    let invUsageΠΣ δ▸F _ _ = inv-usage-ΠΣ γ▸t
        [Γ] , _ , _ = fundamental Γ⊢F:U δ▸F
        [U] , ⊩ʳΠΣ = ΠΣʳ [Γ] Γ⊢ΠΣ
    in  [Γ] , [U] , ⊩ʳΠΣ
  fundamental (ℕⱼ ⊢Γ) γ▸t = ℕʳ ⊢Γ
  fundamental (Emptyⱼ ⊢Γ) γ▸t = Emptyʳ ⊢Γ
  fundamental (Unitⱼ ⊢Γ ok) _ = Unitʳ ⊢Γ ok
  fundamental (var ⊢Γ x∷A∈Γ) γ▸t =
    let [Γ] = F.valid ⊢Γ
        [A] , ⊩ʳx = fundamentalVar well-formed [Γ] x∷A∈Γ γ▸t
    in  [Γ] , [A] , ⊩ʳx
  fundamental
    (lamⱼ {F = F} {t = t} {G = G} {p = p} {q = q} Γ⊢F Γ⊢t:G ok) γ▸t =
    let invUsageLam {δ = δ} δ▸t δ≤γ = inv-usage-lam γ▸t
        [ΓF] , [G]′ , ⊩ʳt = fundamental Γ⊢t:G δ▸t
        [Γ] , [F] = F.fundamental Γ⊢F
        [G] = IS.irrelevance {A = G} [ΓF] ([Γ] ∙ [F]) [G]′
        [Γ]′ , [G]″ , [t]′ = F.fundamentalTerm Γ⊢t:G
        [t] = IS.irrelevanceTerm {A = G} {t = t}
                [Γ]′ ([Γ] ∙ [F]) [G]″ [G] [t]′
        ⊩ʳt′ = irrelevance {A = G} {t = t}
                 [ΓF] ([Γ] ∙ [F]) [G]′ [G] ⊩ʳt
        ⊩ʳλt = lamʳ {t = t} [Γ] [F] [G] [t] ⊩ʳt′ ok
        [Π] = Πᵛ [Γ] [F] [G] ok
    in  [Γ] , [Π] ,
        subsumption-≤ well-formed {A = Π p , q ▷ F ▹ G} {t = lam p t}
          [Γ] [Π] ⊩ʳλt δ≤γ
  fundamental
    (_∘ⱼ_ {t = t} {p = p} {q = q} {F = F} {G = G} {u = u} Γ⊢t:Π Γ⊢u:F)
    γ▸t =
    let invUsageApp δ▸t η▸u γ≤δ+pη = inv-usage-app γ▸t
        [Γ]′ , [Π]′ , ⊩ʳt′ = fundamental Γ⊢t:Π δ▸t
        [Γ] , [F] , ⊩ʳu = fundamental Γ⊢u:F η▸u
        [Π] = IS.irrelevance {A = Π p , q ▷ F ▹ G} [Γ]′ [Γ] [Π]′
        ⊩ʳt = irrelevance {A = Π p , q ▷ F ▹ G} {t = t}
                [Γ]′ [Γ] [Π]′ [Π] ⊩ʳt′
        [Γ]″ , [F]′ , [u]′ = F.fundamentalTerm Γ⊢u:F
        [u] = IS.irrelevanceTerm {A = F} {t = u}
                [Γ]″ [Γ] [F]′ [F] [u]′
        [G[u]] , ⊩ʳt∘u = appʳ {F = F} {G = G} {u = u} {t = t}
                           [Γ] [F] [Π] [u] ⊩ʳt ⊩ʳu
    in  [Γ] , [G[u]] ,
        subsumption-≤ well-formed {A = G [ u ]₀} {t = t ∘⟨ p ⟩ u}
          [Γ] [G[u]] ⊩ʳt∘u γ≤δ+pη
  fundamental
    (prodⱼ {F = F} {G = G} {t = t} {u = u} {k = 𝕤}
       Γ⊢F Γ⊢G Γ⊢t:F Γ⊢u:G ok)
    γ▸t =
    let invUsageProdˢ δ▸t η▸u γ≤pδ∧η = inv-usage-prodˢ γ▸t
        [Γ]₁ , [F] , ⊩ʳt = fundamental Γ⊢t:F δ▸t
        [Γ]₂ , [G[t]]′ , ⊩ʳu = fundamental Γ⊢u:G η▸u
        [Γ] = [Γ]₁
        [Γ]₃ , [G]′ = F.fundamental Γ⊢G
        [G] = IS.irrelevance {A = G} [Γ]₃ ([Γ] ∙ [F]) [G]′
        [G[t]] = IS.irrelevance {A = G [ t ]₀} [Γ]₂ [Γ] [G[t]]′
        [Γ]₄ , [F]₄ , [t]′ = F.fundamentalTerm Γ⊢t:F
        [t] = IS.irrelevanceTerm {A = F} {t = t}
                [Γ]₄ [Γ] [F]₄ [F] [t]′
        [Γ]₅ , [G]₅ , [u]′ = F.fundamentalTerm Γ⊢u:G
        [u] = IS.irrelevanceTerm {A = G [ t ]₀} {t = u}
                [Γ]₅ [Γ] [G]₅ [G[t]] [u]′
        [Σ] , ⊩ʳp =
          prodʳ
            {F = F} {G = G} {t = t} {u = u} {_⊕ᶜ_ = _∧ᶜ_}
            [Γ] [F] [G] [G[t]] [t] [u] ⊩ʳt
            (irrelevance {A = G [ t ]₀} {t = u}
               [Γ]₂ [Γ] [G[t]]′ [G[t]] ⊩ʳu)
            (λ {x} {γ} {δ} γ∧δ≡𝟘 →
               ∧-positiveˡ
                 (PE.trans (PE.sym (lookup-distrib-∧ᶜ γ δ x)) γ∧δ≡𝟘))
            (λ {x} {γ} {δ} γ∧δ≡𝟘 →
               ∧-positiveʳ
                 (PE.trans (PE.sym (lookup-distrib-∧ᶜ γ δ x)) γ∧δ≡𝟘))
            ok
    in  [Γ] , [Σ] ,
        subsumption-≤ well-formed {t = prod! t u} [Γ] [Σ] ⊩ʳp γ≤pδ∧η
  fundamental
    (prodⱼ {F = F} {G = G} {t = t} {u = u} {k = 𝕨}
       Γ⊢F Γ⊢G Γ⊢t:F Γ⊢u:G ok)
    γ▸t =
    let invUsageProdʷ δ▸t η▸u γ≤pδ+η = inv-usage-prodʷ γ▸t
        [Γ]₁ , [F] , ⊩ʳt = fundamental Γ⊢t:F δ▸t
        [Γ]₂ , [G[t]]′ , ⊩ʳu = fundamental Γ⊢u:G η▸u
        [Γ] = [Γ]₁
        [Γ]₃ , [G]′ = F.fundamental Γ⊢G
        [G] = IS.irrelevance {A = G} [Γ]₃ ([Γ] ∙ [F]) [G]′
        [G[t]] = IS.irrelevance {A = G [ t ]₀} [Γ]₂ [Γ] [G[t]]′
        [Γ]₄ , [F]₄ , [t]′ = F.fundamentalTerm Γ⊢t:F
        [t] = IS.irrelevanceTerm {A = F} {t = t}
                [Γ]₄ [Γ] [F]₄ [F] [t]′
        [Γ]₅ , [G]₅ , [u]′ = F.fundamentalTerm Γ⊢u:G
        [u] = IS.irrelevanceTerm {A = G [ t ]₀} {t = u}
                [Γ]₅ [Γ] [G]₅ [G[t]] [u]′
        [Σ] , ⊩ʳp =
          prodʳ
            {F = F} {G = G} {t = t} {u = u} {_⊕ᶜ_ = _+ᶜ_}
            [Γ] [F] [G] [G[t]] [t] [u] ⊩ʳt
            (irrelevance {A = G [ t ]₀} {t = u}
               [Γ]₂ [Γ] [G[t]]′ [G[t]] ⊩ʳu)
            (λ {x} {γ} {δ} γ∧δ≡𝟘 →
               +-positiveˡ $
               PE.trans (PE.sym (lookup-distrib-+ᶜ γ δ x)) γ∧δ≡𝟘)
            (λ {x} {γ} {δ} γ∧δ≡𝟘 →
               +-positiveʳ $
               PE.trans (PE.sym (lookup-distrib-+ᶜ γ δ x)) γ∧δ≡𝟘)
            ok
    in  [Γ] , [Σ] ,
        subsumption-≤ well-formed {t = prod! t u} [Γ] [Σ] ⊩ʳp γ≤pδ+η
  fundamental (fstⱼ {F = F} {t = t} Γ⊢F Γ⊢G Γ⊢t:Σ) γ▸t =
    let invUsageFst m′ m≡m′ᵐ·p δ▸t γ≤δ ok = inv-usage-fst γ▸t
        [Γ] , [Σ] , ⊩ʳt = fundamental Γ⊢t:Σ δ▸t
        [F] , ⊩ʳt₁ =
          fstʳ Γ⊢F Γ⊢G Γ⊢t:Σ [Γ] [Σ] ⊩ʳt
            (fstₘ m′ (▸-cong m≡m′ᵐ·p δ▸t) (PE.sym m≡m′ᵐ·p) ok)
    in  [Γ] , [F] ,
        subsumption-≤ well-formed {t = fst _ t} [Γ] [F] ⊩ʳt₁ γ≤δ
  fundamental (sndⱼ {G = G} {t = t} Γ⊢F Γ⊢G Γ⊢t:Σ) γ▸t =
    let invUsageSnd δ▸t γ≤δ = inv-usage-snd γ▸t
        [Γ] , [Σ] , ⊩ʳt = fundamental Γ⊢t:Σ δ▸t
        [G] , ⊩ʳt₂ = sndʳ Γ⊢F Γ⊢G Γ⊢t:Σ [Γ] [Σ] ⊩ʳt
    in  [Γ] , [G] ,
        subsumption-≤ well-formed {t = snd _ t} [Γ] [G] ⊩ʳt₂ γ≤δ
  fundamental
    (prodrecⱼ {F = F} {G} {A = A} {t = t} {u} {r = r}
       Γ⊢F Γ⊢G Γ⊢A Γ⊢t Γ⊢u _)
    γ▸prodrec =
    let invUsageProdrec {δ = δ} δ▸t η▸u _ ok γ≤pδ+η =
          inv-usage-prodrec γ▸prodrec
        [Γ] , [Σ] , ⊩ʳt = fundamental Γ⊢t δ▸t
        [Γ]₂ , [A₊]₂ , ⊩ʳu = fundamental Γ⊢u η▸u
        [Γ]₃ , [F]₃ = F.fundamental Γ⊢F
        [Γ]₄ , [G]₄ = F.fundamental Γ⊢G
        [Γ]₅ , [A]₅ = F.fundamental Γ⊢A
        [Γ]₆ , [Σ]₆ , [t]₆ = F.fundamentalTerm Γ⊢t
        [Γ]₇ , [A₊]₇ , [u]₇ = F.fundamentalTerm Γ⊢u
        A₊ = A [ prodʷ _ (var (x0 +1)) (var x0) ]↑²
        [F] = IS.irrelevance {A = F} [Γ]₃ [Γ] [F]₃
        [G] = IS.irrelevance {A = G} [Γ]₄ ([Γ] ∙ [F]) [G]₄
        [A₊] = IS.irrelevance {A = A₊} [Γ]₂ ([Γ] ∙ [F] ∙ [G]) [A₊]₂
        [A] = IS.irrelevance {A = A} [Γ]₅ ([Γ] ∙ [Σ]) [A]₅
        [t] = IS.irrelevanceTerm {t = t} [Γ]₆ [Γ] [Σ]₆ [Σ] [t]₆
        [u] = IS.irrelevanceTerm {A = A₊} {u}
                [Γ]₇ ([Γ] ∙ [F] ∙ [G]) [A₊]₇ [A₊] [u]₇
        ⊩ʳu′ = irrelevance {t = u}
                 [Γ]₂ ([Γ] ∙ [F] ∙ [G]) [A₊]₂ [A₊] ⊩ʳu
        r≡𝟘→k≡0 = case closed-or-no-erased-matches of λ where
          (inj₁ nem) → λ r≡𝟘 → ⊥-elim (nem non-trivial .proj₁ ok r≡𝟘)
          (inj₂ k≡0) → λ _ → k≡0
        [At] , ⊩ʳprodrec =
          prodrecʳ
            [Γ] [F] [G] [Σ] [A] [A₊] [t] [u]
            (λ r≢𝟘 →
               PE.subst (δ ▸ _ ⊩ʳ⟨ _ ⟩ t ∷[_] _ / _ / [Σ])
                 (≢𝟘→ᵐ·≡ r≢𝟘) ⊩ʳt)
            ⊩ʳu′ r≡𝟘→k≡0
    in  [Γ] , [At] ,
        subsumption-≤ well-formed {t = prodrec _ _ _ A t u}
          [Γ] [At] ⊩ʳprodrec γ≤pδ+η
  fundamental (zeroⱼ ⊢Γ) γ▸t = zeroʳ ⊢Γ
  fundamental (sucⱼ {n = t} Γ⊢t:ℕ) γ▸t =
    let invUsageSuc δ▸t γ≤δ = inv-usage-suc γ▸t
        [Γ] , [ℕ] , ⊩ʳt = fundamental Γ⊢t:ℕ δ▸t
        δ⊩ʳsuct = sucʳ [Γ] [ℕ] ⊩ʳt Γ⊢t:ℕ
        γ⊩ʳsuct =
          subsumption-≤ well-formed {A = ℕ} {t = suc t}
            [Γ] [ℕ] δ⊩ʳsuct γ≤δ
    in  [Γ] , [ℕ] , γ⊩ʳsuct
  fundamental
    (natrecⱼ {A = A} {z = z} {s = s} {p = p} {q = q} {r = r} {n = n}
       Γ⊢A Γ⊢z:A Γ⊢s:A Γ⊢n:ℕ)
    γ▸t =
    case inv-usage-natrec γ▸t of λ {
      (invUsageNatrec {δ = δ} {η = η} {θ = θ}
         δ▸z η▸s θ▸n _ γ≤γ′ extra) →
    let [Γ]   , [A₀]  , ⊩ʳz  = fundamental Γ⊢z:A δ▸z
        [ΓℕA] , [A₊]′ , ⊩ʳs′ = fundamental Γ⊢s:A η▸s
        [Γ]′  , [ℕ]′  , ⊩ʳn′ = fundamental Γ⊢n:ℕ θ▸n
        [ℕ] = ℕᵛ {l = ¹} [Γ]
        [Γℕ] = [Γ] ∙ [ℕ]
        [Γℕ]′ , [A]′ = F.fundamental Γ⊢A
        [A] = IS.irrelevance {A = A} [Γℕ]′ [Γℕ] [A]′
        [A₊] = IS.irrelevance {A = A [ suc (var x1) ]↑²}
                              [ΓℕA] ([Γℕ] ∙ [A]) [A₊]′
        [Γ]ᶻ , [A]ᶻ , [z]′ = F.fundamentalTerm Γ⊢z:A
        [z] = IS.irrelevanceTerm {A = A [ zero ]₀} {t = z}
                [Γ]ᶻ [Γ] [A]ᶻ [A₀] [z]′
        [Γ]ˢ , [A]ˢ , [s]′ = F.fundamentalTerm Γ⊢s:A
        [s] = IS.irrelevanceTerm
                {A = A [ suc (var x1) ]↑²} {t = s}
                [Γ]ˢ ([Γℕ] ∙ [A]) [A]ˢ [A₊] [s]′
        [Γ]ⁿ , [ℕ]ⁿ , [n]′ = F.fundamentalTerm Γ⊢n:ℕ
        [n] = IS.irrelevanceTerm {A = ℕ} {t = n}
                [Γ]ⁿ [Γ] [ℕ]ⁿ [ℕ] [n]′
        ⊩ʳs = irrelevance
                {A = A [ suc (var x1) ]↑²} {t = s}
                [ΓℕA] ([Γℕ] ∙ [A]) [A₊]′ [A₊] ⊩ʳs′
        ⊩ʳn = irrelevance {A = ℕ} {t = n} [Γ]′ [Γ] [ℕ]′ [ℕ] ⊩ʳn′
        [A[n]] , ⊩ʳnatrec =
          natrecʳ {A = A} {z = z} {s = s} {m = n}
            [Γ] [A] [A₊] [A₀] [z] [s] [n] ⊩ʳz ⊩ʳs ⊩ʳn
            (λ x → case extra of λ where
               invUsageNatrecNr →
                 nrᶜ p r δ η θ ⟨ x ⟩ PE.≡ 𝟘                        →⟨ PE.trans (PE.sym (nrᶜ-⟨⟩ δ)) ⟩
                 nr p r (δ ⟨ x ⟩) (η ⟨ x ⟩) (θ ⟨ x ⟩) PE.≡ 𝟘       →⟨ (λ hyp →
                                                                         case nr-positive hyp of λ {
                                                                           (p , q , r) → p , r , q }) ⟩
                 δ ⟨ x ⟩ PE.≡ 𝟘 × θ ⟨ x ⟩ PE.≡ 𝟘 × η ⟨ x ⟩ PE.≡ 𝟘  □
               (invUsageNatrecNoNr {χ = χ} χ≤δ _ χ≤θ fix) →
                 χ ⟨ x ⟩ PE.≡ 𝟘                                    →⟨ (λ hyp →
                                                                           ≤ᶜ→⟨⟩≡𝟘→⟨⟩≡𝟘 χ≤δ hyp
                                                                         , ≤ᶜ→⟨⟩≡𝟘→⟨⟩≡𝟘 χ≤θ hyp
                                                                         , ⟨⟩≡𝟘→⟨⟩≡𝟘-fixpoint fix hyp) ⟩
                 δ ⟨ x ⟩ PE.≡ 𝟘 × θ ⟨ x ⟩ PE.≡ 𝟘 × η ⟨ x ⟩ PE.≡ 𝟘  □)
    in  [Γ] , [A[n]] ,
        λ {_ _} →
          subsumption-≤ well-formed
            {A = A [ n ]₀} {t = natrec p q r A z s n}
            [Γ] [A[n]] ⊩ʳnatrec γ≤γ′ }
  fundamental
    {Γ = Γ} {γ = γ}
    (emptyrecⱼ {A = A} {t = t} {p = p} ⊢A Γ⊢t:Empty) γ▸t =
    let invUsageemptyrec δ▸t _ γ≤δ = inv-usage-emptyrec γ▸t
        [Γ] , [Empty] , ⊩ʳt = fundamental Γ⊢t:Empty δ▸t
        [Γ]′ , [A]′ = F.fundamental ⊢A
        [A] = IS.irrelevance {A = A} [Γ]′ [Γ] [A]′
        [Γ]″ , [Empty]′ , [t]′ = F.fundamentalTerm Γ⊢t:Empty
        [t] = IS.irrelevanceTerm {A = Empty} {t = t}
                [Γ]″ [Γ] [Empty]′ [Empty] [t]′
        γ⊩ʳemptyrec = emptyrecʳ {A = A} {t = t} {p = p}
                        [Γ] [Empty] [A] [t]
    in  [Γ] , [A] , γ⊩ʳemptyrec
  fundamental (starⱼ ⊢Γ ok) _ = starʳ ⊢Γ ok
  fundamental (unitrecⱼ {A = A} {t} {u} ⊢A ⊢t:Unit ⊢u:A₊ ok) γ▸ur =
    let invUsageUnitrec δ▸t η▸u _ ok′ γ≤γ′ = inv-usage-unitrec γ▸ur
        [Γ] , [Unit] , ⊩ʳt = fundamental ⊢t:Unit δ▸t
        [Γ]₁ , [A₊]₁ , ⊩ʳu′ = fundamental ⊢u:A₊ η▸u
        [Γ]₂ , [A]₂ = F.fundamental ⊢A
        [Γ]₃ , [Unit]₃ , [t]₃ = F.fundamentalTerm ⊢t:Unit
        [Γ]₄ , [A₊]₄ , [u]₄ = F.fundamentalTerm ⊢u:A₊
        [A] = IS.irrelevance [Γ]₂ ([Γ] ∙ [Unit]) [A]₂
        [A₊] = IS.irrelevance [Γ]₁ [Γ] [A₊]₁
        [t] = IS.irrelevanceTerm {t = t} [Γ]₃ [Γ] [Unit]₃ [Unit] [t]₃
        [u] = IS.irrelevanceTerm {t = u} [Γ]₄ [Γ] [A₊]₄ [A₊] [u]₄
        ⊩ʳu = irrelevance {t = u} [Γ]₁ [Γ] [A₊]₁ [A₊] ⊩ʳu′
        p≡𝟘→k≡0 = λ p≡𝟘 → case closed-or-no-erased-matches of λ where
          (inj₁ nem) → ⊥-elim (nem non-trivial .proj₂ .proj₁ ok′ p≡𝟘)
          (inj₂ k≡0) → k≡0
        [Aₜ] , ⊩ʳur = unitrecʳ {u = u} [Γ] ok [Unit] [A] [A₊] [t] [u] ⊩ʳt ⊩ʳu p≡𝟘→k≡0
    in  [Γ] , [Aₜ] , subsumption-≤ well-formed {t = unitrec _ _ A t u} [Γ] [Aₜ] ⊩ʳur γ≤γ′
  fundamental (Idⱼ ⊢A ⊢t ⊢u) _ =
    Idʳ ⊢A ⊢t ⊢u
  fundamental (rflⱼ ⊢t) _ =
    rflʳ ⊢t
  fundamental {γ} (Jⱼ {A} {t} {B} {u} {v} {w} _ ⊢t ⊢B ⊢u ⊢v ⊢w) ▸J =
    case F.fundamentalTerm ⊢t of λ {
      (⊩Γ , ⊩A , ⊩t) →
    case (λ {k Δ σ} →
            F.fundamentalTerm′ ⊩A ⊢v
              {k = k} {Δ = Δ} {σ = σ}) of λ {
      ⊩v →
    let ⊩Id-t-v        = Idᵛ {t = t} ⊩A ⊩t ⊩v
        ⊩Id-wk1-t[v]-v = PE.subst (_ ⊩ᵛ⟨ ¹ ⟩_/ ⊩Γ) ≡Id-wk1-wk1-0[]₀ ⊩Id-t-v
        ⊩wk1-A         = wk1ᵛ _ ⊩A ⊩A
    in
    case substD
           {⊩B = Idᵛ ⊩wk1-A (wk1Termᵛ t ⊩A ⊩A ⊩t)
                   (V.varᵛ here (_ ∙ ⊩A) ⊩wk1-A)}
           ⊩v ⊩Id-wk1-t[v]-v
           (F.fundamentalTerm′ ⊩Id-wk1-t[v]-v $
            PE.subst (_⊢_∷_ _ _) ≡Id-wk1-wk1-0[]₀ ⊢w)
           (F.fundamental′ ⊢B) of λ {
      ⊩B[v,w] →
      ⊩Γ
    , ⊩B[v,w]
    , (λ {_ _} →
         case inv-usage-J ▸J of λ where
           (invUsageJ₀ em _ _ _ ▸u _ _ γ≤) →
             case fundamental′ ⊢u ▸u of λ {
               (⊩B[t,rfl] , ⊩ʳu) →
             Jʳ ⊢t ⊢B ⊢u ⊢v ⊢w ⊩B[t,rfl] ⊩B[v,w] γ≤ ⊩ʳu
               (inj₁ $ case closed-or-no-erased-matches of λ where
                  (inj₂ k≡0) → k≡0
                  (inj₁ nem) →
                    ⊥-elim (nem non-trivial .proj₂ .proj₂ .proj₂ .proj₁ em)) }
           (invUsageJ {γ₂} {γ₃} {γ₄} {γ₅} {γ₆} _ _ _ _ ▸u _ ▸w γ≤) →
             case fundamental′ ⊢u ▸u of λ {
               (⊩B[t,rfl] , ⊩ʳu) →
             subsumption {t = J _ _ A t B u v w} _ ⊩B[v,w]
               (Jʳ ⊢t ⊢B ⊢u ⊢v ⊢w ⊩B[t,rfl] ⊩B[v,w]
                  (∧ᶜ-decreasingˡ γ₄ _) ⊩ʳu
                  (inj₂
                     ( _ , _ , _ , _
                     , ∧ᶜ-decreasingʳ γ₄ _
                     , fundamental″ ⊩Id-t-v ⊢w ▸w
                     )))
               (λ x →
                  γ ⟨ x ⟩ PE.≡ 𝟘                                        →⟨ ≤ᶜ→⟨⟩≡𝟘→⟨⟩≡𝟘 γ≤ ⟩
                  (ω ·ᶜ (γ₂ ∧ᶜ γ₃ ∧ᶜ γ₄ ∧ᶜ γ₅ ∧ᶜ γ₆)) ⟨ x ⟩ PE.≡ 𝟘      →⟨ ·ᶜ-zero-product-⟨⟩ (γ₂ ∧ᶜ _) ⟩
                  ω PE.≡ 𝟘 ⊎ (γ₂ ∧ᶜ γ₃ ∧ᶜ γ₄ ∧ᶜ γ₅ ∧ᶜ γ₆) ⟨ x ⟩ PE.≡ 𝟘  →⟨ (λ { (inj₁ ω≡𝟘) → ⊥-elim (ω≢𝟘 ω≡𝟘); (inj₂ hyp) → hyp }) ⟩
                  (γ₂ ∧ᶜ γ₃ ∧ᶜ γ₄ ∧ᶜ γ₅ ∧ᶜ γ₆) ⟨ x ⟩ PE.≡ 𝟘             →⟨ proj₂ ∘→ ∧ᶜ-positive-⟨⟩ γ₅ ∘→
                                                                           ≤ᶜ→⟨⟩≡𝟘→⟨⟩≡𝟘 {γ = γ₄ ∧ᶜ _}
                                                                             (≤ᶜ-reflexive $
                                                                              ≈ᶜ-trans
                                                                                (≈ᶜ-trans (≈ᶜ-sym (∧ᶜ-assoc _ _ _)) $
                                                                                 ∧ᶜ-congʳ (∧ᶜ-comm _ _)) $
                                                                              ∧ᶜ-assoc _ _ _) ∘→
                                                                           proj₂ ∘→ ∧ᶜ-positive-⟨⟩ γ₃ ∘→
                                                                           proj₂ ∘→ ∧ᶜ-positive-⟨⟩ γ₂ ⟩
                  (γ₄ ∧ᶜ γ₆) ⟨ x ⟩ PE.≡ 𝟘                               □) }) }}}
  fundamental {γ} (Kⱼ {t} {A} {B} {u} {v} ⊢t ⊢B ⊢u ⊢v ok) ▸K =
    case F.fundamentalTerm ⊢t of λ {
      (⊩Γ , ⊩A , ⊩t) →
    let ⊩Id-t-t = Idᵛ ⊩A ⊩t ⊩t in
    case substS _ ⊩Id-t-t (F.fundamental′ ⊢B)
           (F.fundamentalTerm′ ⊩Id-t-t ⊢v) of λ {
      ⊩B[v] →
      ⊩Γ
    , ⊩B[v]
    , (λ {_ _} →
         case inv-usage-K ▸K of λ where
           (invUsageK₀ em _ _ _ ▸u _ γ≤) →
             case fundamental′ ⊢u ▸u of λ {
               (⊩B[rfl] , ⊩ʳu) →
             Kʳ ⊢t ⊢B ⊢u ⊢v ok ⊩B[rfl] ⊩B[v] γ≤ ⊩ʳu
               (inj₁ $ case closed-or-no-erased-matches of λ where
                  (inj₂ k≡0) → k≡0
                  (inj₁ nem) →
                    ⊥-elim (nem non-trivial .proj₂ .proj₂ .proj₂ .proj₂ em)) }
           (invUsageK {γ₂} {γ₃} {γ₄} {γ₅} _ _ _ _ ▸u ▸v γ≤) →
             case fundamental′ ⊢u ▸u of λ {
               (⊩B[rfl] , ⊩ʳu) →
             subsumption {t = K _ A t B u v} _ ⊩B[v]
               (Kʳ ⊢t ⊢B ⊢u ⊢v ok ⊩B[rfl] ⊩B[v]
                  (∧ᶜ-decreasingˡ γ₄ _) ⊩ʳu
                  (inj₂
                     ( _ , _ , _
                     , ∧ᶜ-decreasingʳ γ₄ _
                     , fundamental″ ⊩Id-t-t ⊢v ▸v
                     )))
               (λ x →
                  γ ⟨ x ⟩ PE.≡ 𝟘                                  →⟨ ≤ᶜ→⟨⟩≡𝟘→⟨⟩≡𝟘 γ≤ ⟩
                  (ω ·ᶜ (γ₂ ∧ᶜ γ₃ ∧ᶜ γ₄ ∧ᶜ γ₅)) ⟨ x ⟩ PE.≡ 𝟘      →⟨ ·ᶜ-zero-product-⟨⟩ (γ₂ ∧ᶜ _) ⟩
                  ω PE.≡ 𝟘 ⊎ (γ₂ ∧ᶜ γ₃ ∧ᶜ γ₄ ∧ᶜ γ₅) ⟨ x ⟩ PE.≡ 𝟘  →⟨ (λ { (inj₁ ω≡𝟘) → ⊥-elim (ω≢𝟘 ω≡𝟘); (inj₂ hyp) → hyp }) ⟩
                  (γ₂ ∧ᶜ γ₃ ∧ᶜ γ₄ ∧ᶜ γ₅) ⟨ x ⟩ PE.≡ 𝟘             →⟨ proj₂ ∘→ ∧ᶜ-positive-⟨⟩ γ₃ ∘→
                                                                     proj₂ ∘→ ∧ᶜ-positive-⟨⟩ γ₂ ⟩
                  (γ₄ ∧ᶜ γ₅) ⟨ x ⟩ PE.≡ 𝟘                         □) }) }}
  fundamental ([]-congⱼ ⊢t ⊢u ⊢v ok) _ =
    []-congʳ
      (case closed-or-no-erased-matches of λ where
         (inj₁ nem) → ⊥-elim (nem non-trivial .proj₂ .proj₂ .proj₁ ok)
         (inj₂ k≡0) → k≡0)
      ⊢t ⊢u ⊢v ok
  fundamental (conv {t = t} {A = A} {B = B} Γ⊢t:A A≡B) γ▸t =
    let [Γ] , [A] , ⊩ʳt = fundamental Γ⊢t:A γ▸t
        Γ⊢B = syntacticTerm (conv Γ⊢t:A A≡B)
        [Γ]′ , [B]′ = F.fundamental Γ⊢B
        [B] = IS.irrelevance {A = B} [Γ]′ [Γ] [B]′
    in  [Γ] , [B] ,
        convʳ {A = A} {B = B} {t = t} [Γ] [A] [B] A≡B ⊩ʳt

  -- A fundamental lemma for terms in fully erased contexts.
  --
  -- Note the assumptions of the local module Fundamental.

  fundamentalErased :
    Δ ⊢ t ∷ A → 𝟘ᶜ ▸[ m ] t →
    ∃ λ ([A] : Δ ⊩⟨ ¹ ⟩ A) → t ®⟨ ¹ ⟩ erase t ∷ A ◂ ⌜ m ⌝ / [A]
  fundamentalErased {t = t} {A = A} {m = m} ⊢t 𝟘▸t =
    [A]′ , lemma m ⊩ʳt
    where
    [Δ]-[A]-⊩ʳt = fundamental ⊢t 𝟘▸t
    [Δ] = [Δ]-[A]-⊩ʳt .proj₁
    [A] = [Δ]-[A]-⊩ʳt .proj₂ .proj₁
    ⊩ʳt = [Δ]-[A]-⊩ʳt .proj₂ .proj₂
    [id]′ = idSubstS [Δ]
    ⊢Δ′ = soundContext [Δ]
    [id] = IS.irrelevanceSubst [Δ] [Δ] ⊢Δ′ well-formed [id]′
    [idA] = proj₁ (unwrap [A] {σ = idSubst} well-formed [id])
    [A]′ = I.irrelevance′ (subst-id A) [idA]

    lemma :
      ∀ m →
      𝟘ᶜ ▸ Δ ⊩ʳ⟨ ¹ ⟩ t ∷[ m ] A / [Δ] / [A] →
      t ®⟨ ¹ ⟩ erase t ∷ A ◂ ⌜ m ⌝ / [A]′
    lemma 𝟘ᵐ with is-𝟘? 𝟘
    ... | yes 𝟘≡𝟘 = _
    ... | no 𝟘≢𝟘 = ⊥-elim (𝟘≢𝟘 PE.refl)

    lemma 𝟙ᵐ ⊩ʳt with is-𝟘? 𝟙
    ... | yes 𝟙≡𝟘 = ⊥-elim (non-trivial 𝟙≡𝟘)
    ... | no 𝟙≢𝟘 =
      PE.subst₂ (λ x y → x ®⟨ ¹ ⟩ y ∷ A / [A]′)
        (subst-id t) (TP.subst-id (erase t)) t®t″
      where
      id®id′ = erasedSubst {σ′ = T.idSubst} [Δ] [id]
      t®t′ = ⊩ʳt [id] id®id′
      t®t″ = irrelevanceTerm′ (subst-id A) [idA] [A]′ t®t′

  opaque

    -- A variant of fundamentalErased.

    fundamentalErased-𝟙ᵐ :
      Δ ⊢ t ∷ A → 𝟘ᶜ ▸[ 𝟙ᵐ ] t →
      t ®⟨ ¹ ⟩ erase t ∷ A
    fundamentalErased-𝟙ᵐ ⊢t ▸t =
      case fundamentalErased ⊢t ▸t of λ {
        (⊩A , t®t) →
      hidden-®-intro ⊩A (t®t ◀≢𝟘 non-trivial) }
