------------------------------------------------------------------------
-- The fundamental lemma of the logical relation.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.EqualityRelation
import Definition.Typed
open import Definition.Typed.Restrictions
import Definition.Untyped
open import Tools.Empty
open import Tools.Sum hiding (id)
import Tools.PropositionalEquality as PE

module Graded.Erasure.LogicalRelation.Fundamental
  {a} {M : Set a}
  {𝕄 : Modality M}
  (open Modality 𝕄)
  (TR : Type-restrictions 𝕄)
  (UR : Usage-restrictions 𝕄)
  ⦃ 𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet ⦄
  {{eqrel : EqRelSet TR}}
  where

open Definition.Untyped M
open Definition.Typed TR
open EqRelSet {{...}}

open import Definition.LogicalRelation TR hiding (_≤_)
open import Definition.LogicalRelation.Hidden TR
import Definition.LogicalRelation.Properties TR as LP
open import Definition.LogicalRelation.Substitution TR
open import Definition.LogicalRelation.Substitution.Properties TR
open import Definition.LogicalRelation.Substitution.Introductions.Pi TR
open import Definition.LogicalRelation.Substitution.Introductions.Nat TR
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
open import Definition.Typed.Properties TR

import Graded.Erasure.LogicalRelation
open import Graded.Erasure.LogicalRelation.Assumptions TR
open import Graded.Erasure.LogicalRelation.Fundamental.Assumptions TR UR
import Graded.Erasure.LogicalRelation.Fundamental.Application
import Graded.Erasure.LogicalRelation.Fundamental.Empty
import Graded.Erasure.LogicalRelation.Fundamental.Identity
import Graded.Erasure.LogicalRelation.Fundamental.Lambda
import Graded.Erasure.LogicalRelation.Fundamental.Nat
import Graded.Erasure.LogicalRelation.Fundamental.Prodrec
import Graded.Erasure.LogicalRelation.Fundamental.Product
import Graded.Erasure.LogicalRelation.Fundamental.Unit
import Graded.Erasure.LogicalRelation.Conversion
import Graded.Erasure.LogicalRelation.Hidden
import Graded.Erasure.LogicalRelation.Irrelevance
import Graded.Erasure.LogicalRelation.Subsumption

open import Graded.Erasure.Target as T using (Strictness)
open import Graded.Erasure.Extraction 𝕄
import Graded.Erasure.Target.Properties as TP

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
open import Tools.Relation
import Tools.PropositionalEquality as PE

private
  variable
     l n : Nat
     Γ Δ : Con Term n
     t u A B : Term n
     γ δ : Conₘ n
     p q : M
     x : Fin n
     m : Mode

-- A lemma.

module _ (⊢Δ : ⊢ Δ) {s : Strictness} where

  open Graded.Erasure.LogicalRelation.Hidden
         (record { ⊢Δ = ⊢Δ; str = s })

  opaque

    -- A fundamental lemma for variables.

    fundamentalVar :
      ⊢ Γ →
      x ∷ A ∈ Γ →
      γ ▸[ m ] var x →
      γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ var x ∷[ m ] A
    fundamentalVar {x} {A} {γ} {m} ⊢Γ x∈Γ ▸x =
      ▸⊩ʳ∷⇔ .proj₂
        ( wf-⊩ᵛ∷ (emb-⊩ᵛ∷ LP.≤¹ (varᵛ x∈Γ (F.valid ⊢Γ) .proj₂))
        , λ {σ = σ} {σ′ = σ′} _ σ®σ′ →
            case ®∷[]◂→ σ®σ′ x∈Γ of λ
              (l , _ , _ , σx®σ′x) →
                                                         $⟨ σx®σ′x ⟩
            σ x ®⟨ l ⟩ σ′ x ∷ A [ σ ] ◂ ⌜ m ⌝ · γ ⟨ x ⟩  →⟨ subsumption-®∷◂ (lemma m (inv-usage-var ▸x)) ⟩
            σ x ®⟨ l ⟩ σ′ x ∷ A [ σ ] ◂ ⌜ m ⌝            →⟨ emb-®∷◂ LP.≤¹ ⟩
            σ x ®⟨ ¹ ⟩ σ′ x ∷ A [ σ ] ◂ ⌜ m ⌝            □
        )
      where
      lemma :
        ∀ m →
        γ ≤ᶜ 𝟘ᶜ , x ≔ ⌜ m ⌝ →
        ⌜ m ⌝ · γ ⟨ x ⟩ PE.≡ 𝟘 →
        ⌜ m ⌝ PE.≡ 𝟘
      lemma 𝟘ᵐ = λ _ _ → PE.refl
      lemma 𝟙ᵐ = curry (
        γ ≤ᶜ 𝟘ᶜ , x ≔ 𝟙 × 𝟙 · γ ⟨ x ⟩ PE.≡ 𝟘  →⟨ Σ.map (PE.subst (_≤_ _) (update-lookup 𝟘ᶜ x) ∘→ lookup-monotone _)
                                                   (PE.trans (PE.sym (·-identityˡ _))) ⟩
        γ ⟨ x ⟩ ≤ 𝟙 × γ ⟨ x ⟩ PE.≡ 𝟘          →⟨ uncurry (flip (PE.subst (_≤ _))) ⟩
        𝟘 ≤ 𝟙                                 →⟨ 𝟘≰𝟙 ⟩
        ⊥                                     →⟨ ⊥-elim ⟩
        𝟙 PE.≡ 𝟘                              □)

-- The fundamental lemma, and a variant for terms in fully erased
-- contexts.

module Fundamental
  (FA : Fundamental-assumptions Δ)
  {s : Strictness}
  where

  open Fundamental-assumptions FA

  private

    as : Assumptions
    as = record { ⊢Δ = well-formed; str = s }

  open Graded.Erasure.LogicalRelation as
  open Graded.Erasure.LogicalRelation.Fundamental.Application as
  open Graded.Erasure.LogicalRelation.Fundamental.Empty UR as consistent
  open Graded.Erasure.LogicalRelation.Fundamental.Identity as
  open Graded.Erasure.LogicalRelation.Fundamental.Lambda non-trivial as
  open Graded.Erasure.LogicalRelation.Fundamental.Nat as
  open Graded.Erasure.LogicalRelation.Fundamental.Prodrec as
  open Graded.Erasure.LogicalRelation.Fundamental.Product UR as
  open Graded.Erasure.LogicalRelation.Fundamental.Unit as
  open Graded.Erasure.LogicalRelation.Conversion as
  open Graded.Erasure.LogicalRelation.Hidden as
  open Graded.Erasure.LogicalRelation.Irrelevance as
  open Graded.Erasure.LogicalRelation.Subsumption as

  -- The fundamental lemma for the erasure relation.
  --
  -- Note the assumptions of the local module Fundamental.
  --
  -- The main parts of this proof are located in Graded.Erasure.LogicalRelation.Fundamental.X
  -- The general proof strategy of these is the following:
  -- To show that t is valid, find t′ in whnf such that t ⇒* t′ and show that t′ is valid.
  -- The result that t is valid then follows from the logical relation being closed under
  -- reduction (see Graded.Erasure.LogicalRelation.Reduction).

  opaque
    unfolding _▸_⊩ʳ⟨_⟩_∷[_]_

    fundamental :
      Γ ⊢ t ∷ A → γ ▸[ m ] t →
      ∃₂ λ ([Γ] : ⊩ᵛ Γ) ([A] : Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ]) →
        γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ t ∷[ m ] A / [Γ] / [A]
    fundamental {m = 𝟘ᵐ} ⊢t _ with is-𝟘? 𝟘
    ... | yes 𝟘≡𝟘 =
      case F.fundamental (syntacticTerm ⊢t) of λ ([Γ] , [A]) →
        [Γ] , [A] , _
    ... | no 𝟘≢𝟘 = ⊥-elim (𝟘≢𝟘 PE.refl)
    fundamental Γ⊢ΠΣ@(ΠΣⱼ {F} {G} Γ⊢F:U _ _) γ▸t =
      let invUsageΠΣ δ▸F _ _ = inv-usage-ΠΣ γ▸t
          [Γ] , _ , _ = fundamental Γ⊢F:U δ▸F
          [U] , ⊩ʳΠΣ = ΠΣʳ F G [Γ]
      in  [Γ] , [U] , ⊩ʳΠΣ
    fundamental (ℕⱼ ⊢Γ) _ =
      ℕʳ ⊢Γ
    fundamental (Emptyⱼ ⊢Γ) γ▸t = Emptyʳ ⊢Γ
    fundamental (Unitⱼ ⊢Γ _) _ =
      Unitʳ ⊢Γ
    fundamental (var ⊢Γ x∈Γ) ▸x =
      fundamentalVar well-formed ⊢Γ x∈Γ ▸x
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
          subsumption-≤ {A = Π p , q ▷ F ▹ G} (lam p t) [Π] ⊩ʳλt δ≤γ
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
          subsumption-≤ {A = G [ u ]₀} (t ∘⟨ p ⟩ u) [G[u]] ⊩ʳt∘u γ≤δ+pη
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
      in  [Γ] , [Σ] , subsumption-≤ (prod! t u) [Σ] ⊩ʳp γ≤pδ∧η
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
      in  [Γ] , [Σ] , subsumption-≤ (prod! t u) [Σ] ⊩ʳp γ≤pδ+η
    fundamental (fstⱼ {F = F} {t = t} Γ⊢F Γ⊢G Γ⊢t:Σ) γ▸t =
      let invUsageFst m′ m≡m′ᵐ·p δ▸t γ≤δ ok = inv-usage-fst γ▸t
          [Γ] , [Σ] , ⊩ʳt = fundamental Γ⊢t:Σ δ▸t
          [F] , ⊩ʳt₁ =
            fstʳ Γ⊢F Γ⊢G Γ⊢t:Σ [Γ] [Σ] ⊩ʳt
              (fstₘ m′ (▸-cong m≡m′ᵐ·p δ▸t) (PE.sym m≡m′ᵐ·p) ok)
      in  [Γ] , [F] , subsumption-≤ (fst _ t) [F] ⊩ʳt₁ γ≤δ
    fundamental (sndⱼ {G = G} {t = t} Γ⊢F Γ⊢G Γ⊢t:Σ) γ▸t =
      let invUsageSnd δ▸t γ≤δ = inv-usage-snd γ▸t
          [Γ] , [Σ] , ⊩ʳt = fundamental Γ⊢t:Σ δ▸t
          [G] , ⊩ʳt₂ = sndʳ Γ⊢F Γ⊢G Γ⊢t:Σ [Γ] [Σ] ⊩ʳt
      in  [Γ] , [G] , subsumption-≤ (snd _ t) [G] ⊩ʳt₂ γ≤δ
    fundamental
      {m = 𝟙ᵐ}
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
          subsumption-≤ (prodrec _ _ _ A t u) [At] ⊩ʳprodrec γ≤pδ+η
    fundamental (zeroⱼ ⊢Γ) _ =
      zeroʳ ⊢Γ
    fundamental (sucⱼ {n = t} ⊢t) γ▸suc =
      case inv-usage-suc γ▸suc of λ
        (invUsageSuc δ▸t γ≤δ) →
      subsumption-▸⊩ʳ∷[]-≤ {t = suc t} γ≤δ $
      sucʳ ⊢t (fundamental ⊢t δ▸t)
    fundamental
      (natrecⱼ {A} {z = t} {s = u} {p} {r} {n = v} ⊢A ⊢t ⊢u ⊢v)
      γ▸nr =
      case inv-usage-natrec γ▸nr of λ {
        (invUsageNatrec {δ} {η} {θ} δ▸t η▸u θ▸v _ γ≤χ extra) →
      subsumption-▸⊩ʳ∷[]-≤ {t = natrec _ _ _ A t u v} γ≤χ $
      natrecʳ (F.fundamental-⊩ᵛ ⊢A) ⊢t ⊢u ⊢v (fundamental ⊢t δ▸t)
        (fundamental ⊢u η▸u) (fundamental ⊢v θ▸v)
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
             δ ⟨ x ⟩ PE.≡ 𝟘 × θ ⟨ x ⟩ PE.≡ 𝟘 × η ⟨ x ⟩ PE.≡ 𝟘  □) }
    fundamental
      {Γ = Γ} {γ = γ}
      (emptyrecⱼ {A = A} {t = t} {p = p} ⊢A Γ⊢t:Empty) γ▸t =
      let invUsageEmptyrec δ▸t _ ok γ≤ = inv-usage-emptyrec γ▸t
          [Γ] , [Empty] , ⊩ʳt = fundamental Γ⊢t:Empty δ▸t
          [Γ]′ , [A]′ = F.fundamental ⊢A
          [A] = IS.irrelevance {A = A} [Γ]′ [Γ] [A]′
          [Γ]″ , [Empty]′ , [t]′ = F.fundamentalTerm Γ⊢t:Empty
          [t] = IS.irrelevanceTerm {A = Empty} {t = t}
                  [Γ]″ [Γ] [Empty]′ [Empty] [t]′
          γ⊩ʳemptyrec = emptyrecʳ t ok [Empty] [A] [t] ⊩ʳt
      in  [Γ] , [A] , subsumption-≤ (emptyrec _ A t) [A] γ⊩ʳemptyrec γ≤
    fundamental (starⱼ ⊢Γ ok) _ =
      starʳ ⊢Γ ok
    fundamental {m = 𝟙ᵐ} (unitrecⱼ {A} ⊢A ⊢t ⊢u ok) γ▸ur =
      case inv-usage-unitrec γ▸ur of λ
        (invUsageUnitrec δ▸t η▸u _ ok′ γ≤pδ+η) →
      subsumption-▸⊩ʳ∷[]-≤ {t = unitrec _ _ A _ _} γ≤pδ+η $
      unitrecʳ (F.fundamental-⊩ᵛ ⊢A) (F.fundamental-⊩ᵛ∷ ⊢t)
        (F.fundamental-⊩ᵛ∷ ⊢u) (fundamental ⊢t δ▸t) (fundamental ⊢u η▸u)
        (λ p≡𝟘 → case closed-or-no-erased-matches of λ where
           (inj₁ nem) → ⊥-elim (nem non-trivial .proj₂ .proj₁ ok′ p≡𝟘)
           (inj₂ k≡0) → k≡0)
    fundamental (Idⱼ {A} {t} {u} ⊢A _ _) _ =
      Idʳ {A = A} {t = t} {u = u} (wfTerm ⊢A)
    fundamental (rflⱼ ⊢t) _ =
      rflʳ ⊢t
    fundamental
      {γ} {m = 𝟙ᵐ} (Jⱼ {A} {t} {B} {u} {v} {w} _ _ ⊢B ⊢u _ ⊢w) ▸J =
      case F.fundamental-⊩ᵛ ⊢B of λ
        ⊩B →
      case inv-usage-J ▸J of λ where
        (invUsageJ₀₂ em _ _ _ ▸u _ _ γ≤) →
          Jʳ ⊩B ⊢u ⊢w γ≤ (fundamental ⊢u ▸u)
            (inj₁ $ case closed-or-no-erased-matches of λ where
               (inj₂ k≡0) → k≡0
               (inj₁ nem) →
                 case
                   PE.trans (PE.sym em)
                     (nem non-trivial .proj₂ .proj₂ .proj₂ .proj₁)
                 of λ ())
        (invUsageJ₀₁ {γ₃} {γ₄} em _ _ _ _ _ ▸u _ _ γ≤) →
          subsumption-▸⊩ʳ∷[] {t = J _ _ A t B u v w}
            (λ x →
               γ ⟨ x ⟩ PE.≡ 𝟘                      →⟨ ≤ᶜ→⟨⟩≡𝟘→⟨⟩≡𝟘 γ≤ ⟩
               (ω ·ᶜ (γ₃ +ᶜ γ₄)) ⟨ x ⟩ PE.≡ 𝟘      →⟨ ·ᶜ-zero-product-⟨⟩ (γ₃ +ᶜ _) ⟩
               ω PE.≡ 𝟘 ⊎ (γ₃ +ᶜ γ₄) ⟨ x ⟩ PE.≡ 𝟘  →⟨ (λ { (inj₁ ω≡𝟘) → ⊥-elim (ω≢𝟘 ω≡𝟘); (inj₂ hyp) → hyp }) ⟩
               (γ₃ +ᶜ γ₄) ⟨ x ⟩ PE.≡ 𝟘             →⟨ +ᶜ-⟨⟩-≡-𝟘-→-∧ᶜ-⟨⟩-≡-𝟘 γ₃ ⟩
               (γ₃ ∧ᶜ γ₄) ⟨ x ⟩ PE.≡ 𝟘             □) $
          Jʳ ⊩B ⊢u ⊢w (∧ᶜ-decreasingʳ γ₃ _) (fundamental ⊢u ▸u)
            (inj₁ $ case closed-or-no-erased-matches of λ where
               (inj₂ k≡0) → k≡0
               (inj₁ nem) →
                 case
                   PE.trans (PE.sym em)
                     (nem non-trivial .proj₂ .proj₂ .proj₂ .proj₁)
                 of λ ())
        (invUsageJ {γ₂} {γ₃} {γ₄} {γ₅} {γ₆} _ _ _ _ _ ▸u _ ▸w γ≤) →
          subsumption-▸⊩ʳ∷[] {t = J _ _ A t B u v w}
            (λ x →
               γ ⟨ x ⟩ PE.≡ 𝟘                                        →⟨ ≤ᶜ→⟨⟩≡𝟘→⟨⟩≡𝟘 γ≤ ⟩
               (ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆)) ⟨ x ⟩ PE.≡ 𝟘      →⟨ ·ᶜ-zero-product-⟨⟩ (γ₂ +ᶜ _) ⟩
               ω PE.≡ 𝟘 ⊎ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆) ⟨ x ⟩ PE.≡ 𝟘  →⟨ (λ { (inj₁ ω≡𝟘) → ⊥-elim (ω≢𝟘 ω≡𝟘); (inj₂ hyp) → hyp }) ⟩
               (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆) ⟨ x ⟩ PE.≡ 𝟘             →⟨ proj₂ ∘→ +ᶜ-positive-⟨⟩ γ₅ ∘→
                                                                        ≤ᶜ→⟨⟩≡𝟘→⟨⟩≡𝟘 {γ = γ₄ +ᶜ _}
                                                                          (≤ᶜ-reflexive $
                                                                           ≈ᶜ-trans
                                                                             (≈ᶜ-trans (≈ᶜ-sym (+ᶜ-assoc _ _ _)) $
                                                                              +ᶜ-congʳ (+ᶜ-comm _ _)) $
                                                                           +ᶜ-assoc _ _ _) ∘→
                                                                        proj₂ ∘→ +ᶜ-positive-⟨⟩ γ₃ ∘→
                                                                        proj₂ ∘→ +ᶜ-positive-⟨⟩ γ₂ ⟩
               (γ₄ +ᶜ γ₆) ⟨ x ⟩ PE.≡ 𝟘                               →⟨ +ᶜ-⟨⟩-≡-𝟘-→-∧ᶜ-⟨⟩-≡-𝟘 γ₄ ⟩
               (γ₄ ∧ᶜ γ₆) ⟨ x ⟩ PE.≡ 𝟘                               □)
            (Jʳ ⊩B ⊢u ⊢w (∧ᶜ-decreasingˡ γ₄ _) (fundamental ⊢u ▸u)
               (inj₂ (_ , ∧ᶜ-decreasingʳ γ₄ _ , _ , fundamental ⊢w ▸w)))
    fundamental {γ} {m = 𝟙ᵐ} (Kⱼ {t} {A} {B} {u} {v} _ ⊢B ⊢u ⊢v ok) ▸K =
      case F.fundamental-⊩ᵛ ⊢B of λ
        ⊩B →
      case inv-usage-K ▸K of λ where
        (invUsageK₀₂ em _ _ _ ▸u _ γ≤) →
          Kʳ ⊩B ⊢u ⊢v ok γ≤ (fundamental ⊢u ▸u)
            (inj₁ $ case closed-or-no-erased-matches of λ where
               (inj₂ k≡0) → k≡0
               (inj₁ nem) →
                 case
                   PE.trans (PE.sym em)
                     (nem non-trivial .proj₂ .proj₂ .proj₂ .proj₂)
                 of λ ())
        (invUsageK₀₁ {γ₃} {γ₄} em _ _ _ _ ▸u _ γ≤) →
          subsumption-▸⊩ʳ∷[] {t = K _ A t B u v}
            (λ x →
               γ ⟨ x ⟩ PE.≡ 𝟘                      →⟨ ≤ᶜ→⟨⟩≡𝟘→⟨⟩≡𝟘 γ≤ ⟩
               (ω ·ᶜ (γ₃ +ᶜ γ₄)) ⟨ x ⟩ PE.≡ 𝟘      →⟨ ·ᶜ-zero-product-⟨⟩ (γ₃ +ᶜ _) ⟩
               ω PE.≡ 𝟘 ⊎ (γ₃ +ᶜ γ₄) ⟨ x ⟩ PE.≡ 𝟘  →⟨ (λ { (inj₁ ω≡𝟘) → ⊥-elim (ω≢𝟘 ω≡𝟘); (inj₂ hyp) → hyp }) ⟩
               (γ₃ +ᶜ γ₄) ⟨ x ⟩ PE.≡ 𝟘             →⟨ +ᶜ-⟨⟩-≡-𝟘-→-∧ᶜ-⟨⟩-≡-𝟘 γ₃ ⟩
               (γ₃ ∧ᶜ γ₄) ⟨ x ⟩ PE.≡ 𝟘             □) $
          Kʳ ⊩B ⊢u ⊢v ok (∧ᶜ-decreasingʳ γ₃ _) (fundamental ⊢u ▸u)
            (inj₁ $ case closed-or-no-erased-matches of λ where
               (inj₂ k≡0) → k≡0
               (inj₁ nem) →
                 case
                   PE.trans (PE.sym em)
                     (nem non-trivial .proj₂ .proj₂ .proj₂ .proj₂)
                 of λ ())
        (invUsageK {γ₂} {γ₃} {γ₄} {γ₅} _ _ _ _ _ ▸u ▸v γ≤) →
          subsumption-▸⊩ʳ∷[] {t = K _ A t B u v}
            (λ x →
               γ ⟨ x ⟩ PE.≡ 𝟘                                  →⟨ ≤ᶜ→⟨⟩≡𝟘→⟨⟩≡𝟘 γ≤ ⟩
               (ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅)) ⟨ x ⟩ PE.≡ 𝟘      →⟨ ·ᶜ-zero-product-⟨⟩ (γ₂ +ᶜ _) ⟩
               ω PE.≡ 𝟘 ⊎ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅) ⟨ x ⟩ PE.≡ 𝟘  →⟨ (λ { (inj₁ ω≡𝟘) → ⊥-elim (ω≢𝟘 ω≡𝟘); (inj₂ hyp) → hyp }) ⟩
               (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅) ⟨ x ⟩ PE.≡ 𝟘             →⟨ proj₂ ∘→ +ᶜ-positive-⟨⟩ γ₃ ∘→
                                                                  proj₂ ∘→ +ᶜ-positive-⟨⟩ γ₂ ⟩
               (γ₄ +ᶜ γ₅) ⟨ x ⟩ PE.≡ 𝟘                         →⟨ +ᶜ-⟨⟩-≡-𝟘-→-∧ᶜ-⟨⟩-≡-𝟘 γ₄ ⟩
               (γ₄ ∧ᶜ γ₅) ⟨ x ⟩ PE.≡ 𝟘                         □) $
          Kʳ ⊩B ⊢u ⊢v ok (∧ᶜ-decreasingˡ γ₄ _) (fundamental ⊢u ▸u)
            (inj₂ (_ , ∧ᶜ-decreasingʳ γ₄ _ , _ , fundamental ⊢v ▸v))
    fundamental ([]-congⱼ _ _ ⊢v ok) _ =
      []-congʳ
        (case closed-or-no-erased-matches of λ where
           (inj₁ nem) → ⊥-elim (nem non-trivial .proj₂ .proj₂ .proj₁ ok)
           (inj₂ k≡0) → k≡0)
        ⊢v ok
    fundamental (conv {t} ⊢t A≡B) γ▸t =
      conv-▸⊩ʳ∷ {t = t} (F.fundamental-⊩ᵛ≡ A≡B) (fundamental ⊢t γ▸t)

  -- A fundamental lemma for terms in fully erased contexts.
  --
  -- Note the assumptions of the local module Fundamental.

  fundamentalErased :
    Δ ⊢ t ∷ A → 𝟘ᶜ ▸[ m ] t →
    ∃ λ ([A] : Δ ⊩⟨ ¹ ⟩ A) → t ®⟨ ¹ ⟩ erase s t ∷ A ◂ ⌜ m ⌝ / [A]
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
      t ®⟨ ¹ ⟩ erase s t ∷ A ◂ ⌜ m ⌝ / [A]′
    lemma 𝟘ᵐ with is-𝟘? 𝟘
    ... | yes 𝟘≡𝟘 = _
    ... | no 𝟘≢𝟘 = ⊥-elim (𝟘≢𝟘 PE.refl)

    lemma 𝟙ᵐ ⊩ʳt with is-𝟘? 𝟙
    ... | yes 𝟙≡𝟘 = ⊥-elim (non-trivial 𝟙≡𝟘)
    ... | no 𝟙≢𝟘 =
      PE.subst₂ (λ x y → x ®⟨ ¹ ⟩ y ∷ A / [A]′)
        (subst-id t) (TP.subst-id (erase s t)) t®t″
      where
      id®id′ = erasedSubst {σ′ = T.idSubst} [Δ] [id]
      t®t′ = ⊩ʳt [id] id®id′
      t®t″ = irrelevanceTerm′ (subst-id A) [idA] [A]′ t®t′

  opaque
    unfolding _▸_⊩ʳ⟨_⟩_∷[_]_

    -- A variant of fundamental.

    fundamental-⊩ʳ∷ :
      Γ ⊢ t ∷ A → γ ▸[ m ] t →
      γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ t ∷[ m ] A
    fundamental-⊩ʳ∷ = fundamental

  opaque
    unfolding _®⟨_⟩_∷_◂_

    -- A variant of fundamentalErased.

    fundamentalErased-®∷◂ :
      Δ ⊢ t ∷ A → 𝟘ᶜ ▸[ m ] t →
      t ®⟨ ¹ ⟩ erase s t ∷ A ◂ ⌜ m ⌝
    fundamentalErased-®∷◂ = fundamentalErased

  opaque

    -- Another variant of fundamentalErased.

    fundamentalErased-𝟙ᵐ :
      Δ ⊢ t ∷ A → 𝟘ᶜ ▸[ 𝟙ᵐ ] t →
      t ®⟨ ¹ ⟩ erase s t ∷ A
    fundamentalErased-𝟙ᵐ ⊢t ▸t =
      ®∷→®∷◂ω non-trivial $
      fundamentalErased-®∷◂ ⊢t ▸t
