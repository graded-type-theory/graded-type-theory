------------------------------------------------------------------------
-- The fundamental lemma of the logical relation.
------------------------------------------------------------------------

open import Definition.Modality
open import Definition.Modality.Restrictions.Definitions
open import Definition.Typed.EqualityRelation
import Definition.Typed
open import Definition.Typed.Restrictions
import Definition.Untyped hiding (_∷_)
open import Tools.Empty
open import Tools.Sum hiding (id)
import Tools.PropositionalEquality as PE

module Erasure.LogicalRelation.Fundamental
  {a k} {M : Set a}
  (open Definition.Untyped M)
  (𝕄 : Modality M)
  (open Modality 𝕄)
  (R : Type-restrictions M)
  (open Definition.Typed R)
  {Δ : Con Term k} (⊢Δ : ⊢ Δ)
  (𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet)
  (consistent : ∀ {t} → Δ ⊢ t ∷ Empty → ⊥)
  -- Erased matches are not allowed unless the context
  -- is empty
  (no-erased-matches : No-erased-matches 𝕄 ⊎ k PE.≡ 0)
  {{eqrel : EqRelSet R}}
  where


open EqRelSet {{...}}

open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Properties.Escape R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.MaybeEmbed R
open import Definition.LogicalRelation.Substitution.Properties R
open import Definition.LogicalRelation.Substitution.Weakening R
open import Definition.LogicalRelation.Substitution.Introductions.Pi R
open import Definition.LogicalRelation.Substitution.Introductions.Nat R

import Definition.LogicalRelation.Fundamental R as F
import Definition.LogicalRelation.Irrelevance R as I
import Definition.LogicalRelation.Substitution.Irrelevance R as IS

open import Definition.Modality.Context 𝕄
open import Definition.Modality.Context.Properties 𝕄
open import Definition.Modality.Properties.PartialOrder semiring-with-meet
open import Definition.Modality.Properties.Has-well-behaved-zero
  semiring-with-meet-and-star 𝟘-well-behaved
open import Definition.Modality.Usage 𝕄
open import Definition.Modality.Usage.Inversion 𝕄
open import Definition.Modality.Usage.Properties 𝕄
open import Definition.Mode 𝕄


open import Definition.Untyped.Properties M
open import Definition.Typed.Consequences.Syntactic R

open import Erasure.LogicalRelation 𝕄 R ⊢Δ is-𝟘?
open import Erasure.LogicalRelation.Fundamental.Application 𝕄 R ⊢Δ 𝟘-well-behaved
open import Erasure.LogicalRelation.Fundamental.Empty 𝕄 R ⊢Δ is-𝟘? consistent
open import Erasure.LogicalRelation.Fundamental.Lambda 𝕄 R ⊢Δ is-𝟘? 𝟙≉𝟘
open import Erasure.LogicalRelation.Fundamental.Nat 𝕄 R ⊢Δ is-𝟘?
open import Erasure.LogicalRelation.Fundamental.Natrec 𝕄 R ⊢Δ 𝟘-well-behaved
open import Erasure.LogicalRelation.Fundamental.Prodrec 𝕄 R ⊢Δ 𝟘-well-behaved
open import Erasure.LogicalRelation.Fundamental.Product 𝕄 R ⊢Δ 𝟘-well-behaved
open import Erasure.LogicalRelation.Fundamental.Unit 𝕄 R ⊢Δ is-𝟘?
open import Erasure.LogicalRelation.Conversion 𝕄 R ⊢Δ is-𝟘?
open import Erasure.LogicalRelation.Irrelevance 𝕄 R ⊢Δ is-𝟘?
open import Erasure.LogicalRelation.Subsumption 𝕄 R ⊢Δ is-𝟘?

import Erasure.Target as T
open import Erasure.Extraction 𝕄 is-𝟘?
import Erasure.Target.Properties as TP

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Nullary
open import Tools.Product
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PartialOrder
import Tools.PropositionalEquality as PE

private
  variable
     l n : Nat
     Γ : Con Term n
     t u A B : Term n
     γ δ : Conₘ n
     p q : M
     σ : Subst l n
     x : Fin n
     σ′ : T.Subst l n
     m : Mode

-- Special case of Subsumption

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

-- Fundamental lemma for variables

fundamentalVar′ : ([Γ] : ⊩ᵛ Γ)
                → x ∷ A ∈ Γ
                → γ ≤ᶜ 𝟘ᶜ , x ≔ 𝟙
                → ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
                → (σ®σ′ : σ ®⟨ ¹ ⟩ σ′ ∷[ 𝟙ᵐ ] Γ ◂ γ / [Γ] / [σ])
                → ∃ λ ([A] : Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ]) → σ x ®⟨ ¹ ⟩ σ′ x ∷ subst σ A / proj₁ (unwrap [A] ⊢Δ [σ])
fundamentalVar′ ε ()
fundamentalVar′ {σ = σ} (_∙_ {A = A} [Γ] [A]) here (_ ∙ p≤𝟙)
                ([tailσ] , [headσ]) (σ®σ′ , σ0®σ′0) =
  let [A]′ = proj₁ (unwrap [A] ⊢Δ [tailσ])
      [↑A] = wk1ᵛ {A = A} {F = A} [Γ] [A] [A]
      [↑A]′ = maybeEmbᵛ {A = wk1 A} (_∙_ {A = A} [Γ] [A]) [↑A]
      [σ↑A] = proj₁ (unwrap [↑A]′ {σ = σ} ⊢Δ ([tailσ] , [headσ]))
      A≡A : Δ ⊢ subst (tail σ) A ≡ subst (tail σ) A
      A≡A = refl (escape [A]′)
      A≡A′ = PE.subst (Δ ⊢ subst (tail σ) A ≡_)
                      (PE.sym (wk1-tail A)) A≡A
      σ0®σ′0′ = σ0®σ′0 ◀≢𝟘 λ 𝟙p≡𝟘 →
        𝟙≉𝟘 (𝟘≮ (≤-trans (≤-reflexive (PE.trans (PE.sym 𝟙p≡𝟘) (·-identityˡ _))) p≤𝟙))
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
  ... | no 𝟘≢𝟘 = PE.⊥-elim (𝟘≢𝟘 PE.refl)

  lemma 𝟙ᵐ γ▸x [σ] σ®σ′ with is-𝟘? 𝟙
  ... | yes 𝟙≡𝟘 = PE.⊥-elim (𝟙≉𝟘 𝟙≡𝟘)
  ... | no 𝟙≢𝟘 =
     let [A]′ , t®v = fundamentalVar′ [Γ] x∷A∈Γ (inv-usage-var γ▸x) [σ] σ®σ′
     in  irrelevanceTerm (proj₁ (unwrap [A]′ ⊢Δ [σ]))
           (proj₁ (unwrap [A] ⊢Δ [σ])) t®v

-- The fundamental lemma for the erasure relation.

fundamental : Γ ⊢ t ∷ A → γ ▸[ m ] t
            → ∃₂ λ ([Γ] : ⊩ᵛ Γ) ([A] : Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ])
                 → γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ t ∷[ m ] A / [Γ] / [A]
fundamental {m = 𝟘ᵐ} ⊢t _ with is-𝟘? 𝟘
... | yes 𝟘≡𝟘 =
  case F.fundamental (syntacticTerm ⊢t) of λ ([Γ] , [A]) →
    [Γ] , [A] , _
... | no 𝟘≢𝟘 = PE.⊥-elim (𝟘≢𝟘 PE.refl)
fundamental Γ⊢ΠΣ@(ΠΣⱼ Γ⊢F:U _ _) γ▸t =
  let invUsageΠΣ δ▸F _ _ _ = inv-usage-ΠΣ γ▸t
      [Γ] , _ , _ = fundamental Γ⊢F:U δ▸F
      [U] , ⊩ʳΠΣ = ΠΣʳ [Γ] Γ⊢ΠΣ
  in  [Γ] , [U] , ⊩ʳΠΣ
fundamental (ℕⱼ ⊢Γ) γ▸t = ℕʳ ⊢Γ
fundamental (Emptyⱼ ⊢Γ) γ▸t = Emptyʳ ⊢Γ
fundamental (Unitⱼ ⊢Γ ok) _ = Unitʳ ⊢Γ ok
fundamental (var ⊢Γ x∷A∈Γ) γ▸t =
  let [Γ] = F.valid ⊢Γ
      [A] , ⊩ʳx = fundamentalVar [Γ] x∷A∈Γ γ▸t
  in  [Γ] , [A] , ⊩ʳx
fundamental (lamⱼ {p = p} {q = q} {F = F} {G = G} {t = t} Γ⊢F Γ⊢t:G) γ▸t =
  let invUsageLam {δ = δ} δ▸t δ≤γ = inv-usage-lam γ▸t
      [ΓF] , [G]′ , ⊩ʳt = fundamental Γ⊢t:G δ▸t
      [Γ] , [F] = F.fundamental Γ⊢F
      [G] = IS.irrelevance {A = G} [ΓF] ([Γ] ∙ [F]) [G]′
      [Γ]′ , [G]″ , [t]′ = F.fundamentalTerm Γ⊢t:G
      [t] = IS.irrelevanceTerm {A = G} {t = t} [Γ]′ ([Γ] ∙ [F]) [G]″ [G] [t]′
      ⊩ʳt′ = irrelevance {A = G} {t = t} [ΓF] ([Γ] ∙ [F]) [G]′ [G] ⊩ʳt
      ⊩ʳλt = lamʳ {F = F} {G = G} {t = t} {γ = δ} {p = p} {q = q} [Γ] [F] [G] [t] ⊩ʳt′
      [Π] = Πᵛ {F = F} {G = G} [Γ] [F] [G]
  in  [Γ] , [Π] , subsumption-≤ {A = Π p , q ▷ F ▹ G} {t = lam p t} [Γ] [Π] ⊩ʳλt δ≤γ
fundamental (_∘ⱼ_ {p = p} {q = q} {g = t} {a = u} {F = F} {G = G} Γ⊢t:Π Γ⊢u:F) γ▸t =
  let invUsageApp δ▸t η▸u γ≤δ+pη = inv-usage-app γ▸t
      [Γ]′ , [Π]′ , ⊩ʳt′ = fundamental Γ⊢t:Π δ▸t
      [Γ] , [F] , ⊩ʳu = fundamental Γ⊢u:F η▸u
      [Π] = IS.irrelevance {A = Π p , q ▷ F ▹ G} [Γ]′ [Γ] [Π]′
      ⊩ʳt = irrelevance {A = Π p , q ▷ F ▹ G} {t = t} [Γ]′ [Γ] [Π]′ [Π] ⊩ʳt′
      [Γ]″ , [F]′ , [u]′ = F.fundamentalTerm Γ⊢u:F
      [u] = IS.irrelevanceTerm {A = F} {t = u} [Γ]″ [Γ] [F]′ [F] [u]′
      [G[u]] , ⊩ʳt∘u = appʳ {F = F} {G = G} {u = u} {t = t} [Γ] [F] [Π] [u] ⊩ʳt ⊩ʳu
  in  [Γ] , [G[u]] , subsumption-≤ {A = G [ u ]} {t = t ∘⟨ p ⟩ u} [Γ] [G[u]] ⊩ʳt∘u γ≤δ+pη
fundamental
  (prodⱼ {Σₚ} {F = F} {G = G} {t = t} {u = u} Γ⊢F Γ⊢G Γ⊢t:F Γ⊢u:G ok)
  γ▸t =
  let invUsageProdₚ δ▸t η▸u γ≤pδ∧η = inv-usage-prodₚ γ▸t
      [Γ]₁ , [F] , ⊩ʳt = fundamental Γ⊢t:F δ▸t
      [Γ]₂ , [G[t]]′ , ⊩ʳu = fundamental Γ⊢u:G η▸u
      [Γ] = [Γ]₁
      [Γ]₃ , [G]′ = F.fundamental Γ⊢G
      [G] = IS.irrelevance {A = G} [Γ]₃ ([Γ] ∙ [F]) [G]′
      [G[t]] = IS.irrelevance {A = G [ t ]} [Γ]₂ [Γ] [G[t]]′
      [Γ]₄ , [F]₄ , [t]′ = F.fundamentalTerm Γ⊢t:F
      [t] = IS.irrelevanceTerm {A = F} {t = t} [Γ]₄ [Γ] [F]₄ [F] [t]′
      [Γ]₅ , [G]₅ , [u]′ = F.fundamentalTerm Γ⊢u:G
      [u] = IS.irrelevanceTerm {A = G [ t ]} {t = u} [Γ]₅ [Γ] [G]₅ [G[t]] [u]′
      [Σ] , ⊩ʳp = prodʳ  {F = F} {G = G} {t = t} {u = u} {_⊕ᶜ_ = _∧ᶜ_} [Γ] [F] [G] [G[t]] [t] [u] ⊩ʳt
                        (irrelevance {A = G [ t ]} {t = u} [Γ]₂ [Γ] [G[t]]′ [G[t]] ⊩ʳu)
                        (λ {x} {γ} {δ} γ∧δ≡𝟘 → ∧-positiveˡ (PE.trans (PE.sym (lookup-distrib-∧ᶜ γ δ x)) γ∧δ≡𝟘))
                        (λ {x} {γ} {δ} γ∧δ≡𝟘 → ∧-positiveʳ (PE.trans (PE.sym (lookup-distrib-∧ᶜ γ δ x)) γ∧δ≡𝟘))
                        ok
  in  [Γ] , [Σ] ,
      subsumption-≤ {t = prod! t u} [Γ] [Σ] ⊩ʳp γ≤pδ∧η
fundamental
  (prodⱼ {Σᵣ} {F = F} {G = G} {t = t} {u = u} Γ⊢F Γ⊢G Γ⊢t:F Γ⊢u:G ok)
  γ▸t =
  let invUsageProdᵣ δ▸t η▸u γ≤pδ+η = inv-usage-prodᵣ γ▸t
      [Γ]₁ , [F] , ⊩ʳt = fundamental Γ⊢t:F δ▸t
      [Γ]₂ , [G[t]]′ , ⊩ʳu = fundamental Γ⊢u:G η▸u
      [Γ] = [Γ]₁
      [Γ]₃ , [G]′ = F.fundamental Γ⊢G
      [G] = IS.irrelevance {A = G} [Γ]₃ ([Γ] ∙ [F]) [G]′
      [G[t]] = IS.irrelevance {A = G [ t ]} [Γ]₂ [Γ] [G[t]]′
      [Γ]₄ , [F]₄ , [t]′ = F.fundamentalTerm Γ⊢t:F
      [t] = IS.irrelevanceTerm {A = F} {t = t} [Γ]₄ [Γ] [F]₄ [F] [t]′
      [Γ]₅ , [G]₅ , [u]′ = F.fundamentalTerm Γ⊢u:G
      [u] = IS.irrelevanceTerm {A = G [ t ]} {t = u} [Γ]₅ [Γ] [G]₅ [G[t]] [u]′
      [Σ] , ⊩ʳp = prodʳ {F = F} {G = G} {t = t} {u = u} {_⊕ᶜ_ = _+ᶜ_} [Γ] [F] [G] [G[t]] [t] [u] ⊩ʳt
                        (irrelevance {A = G [ t ]} {t = u} [Γ]₂ [Γ] [G[t]]′ [G[t]] ⊩ʳu)
                        (λ {x} {γ} {δ} γ∧δ≡𝟘 → +-positiveˡ (PE.trans (PE.sym (lookup-distrib-+ᶜ γ δ x)) γ∧δ≡𝟘))
                        (λ {x} {γ} {δ} γ∧δ≡𝟘 → +-positiveʳ (PE.trans (PE.sym (lookup-distrib-+ᶜ γ δ x)) γ∧δ≡𝟘))
                        ok
  in  [Γ] , [Σ] ,
      subsumption-≤ {t = prod! t u} [Γ] [Σ] ⊩ʳp γ≤pδ+η
fundamental (fstⱼ {F = F} {t = t} Γ⊢F Γ⊢G Γ⊢t:Σ) γ▸t =
  let invUsageFst m′ m≡m′ᵐ·p δ▸t γ≤δ ok = inv-usage-fst γ▸t
      [Γ] , [Σ] , ⊩ʳt = fundamental Γ⊢t:Σ δ▸t
      [F] , ⊩ʳt₁ = fstʳ Γ⊢F Γ⊢G Γ⊢t:Σ [Γ] [Σ] ⊩ʳt
                     (fstₘ m′ (▸-cong m≡m′ᵐ·p δ▸t) (PE.sym m≡m′ᵐ·p) ok)
  in  [Γ] , [F] , subsumption-≤ {t = fst _ t} [Γ] [F] ⊩ʳt₁ γ≤δ
fundamental (sndⱼ {G = G} {t = t} Γ⊢F Γ⊢G Γ⊢t:Σ) γ▸t =
  let invUsageSnd δ▸t γ≤δ = inv-usage-snd γ▸t
      [Γ] , [Σ] , ⊩ʳt = fundamental Γ⊢t:Σ δ▸t
      [G] , ⊩ʳt₂ = sndʳ Γ⊢F Γ⊢G Γ⊢t:Σ [Γ] [Σ] ⊩ʳt
  in  [Γ] , [G] , subsumption-≤ {t = snd _ t} [Γ] [G] ⊩ʳt₂ γ≤δ
fundamental (prodrecⱼ {r = r} {t = t} {u} {F} {G} {A} Γ⊢F Γ⊢G Γ⊢A Γ⊢t Γ⊢u) γ▸prodrec =
  let invUsageProdrec {δ = δ} δ▸t η▸u _ P γ≤pδ+η = inv-usage-prodrec γ▸prodrec
      [Γ] , [Σ] , ⊩ʳt = fundamental Γ⊢t δ▸t
      [Γ]₂ , [A₊]₂ , ⊩ʳu = fundamental Γ⊢u η▸u
      [Γ]₃ , [F]₃ = F.fundamental Γ⊢F
      [Γ]₄ , [G]₄ = F.fundamental Γ⊢G
      [Γ]₅ , [A]₅ = F.fundamental Γ⊢A
      [Γ]₆ , [Σ]₆ , [t]₆ = F.fundamentalTerm Γ⊢t
      [Γ]₇ , [A₊]₇ , [u]₇ = F.fundamentalTerm Γ⊢u
      A₊ = A [ prodᵣ _ (var (x0 +1)) (var x0) ]↑²
      [F] = IS.irrelevance {A = F} [Γ]₃ [Γ] [F]₃
      [G] = IS.irrelevance {A = G} [Γ]₄ ([Γ] ∙ [F]) [G]₄
      [A₊] = IS.irrelevance {A = A₊} [Γ]₂ ([Γ] ∙ [F] ∙ [G]) [A₊]₂
      [A] = IS.irrelevance {A = A} [Γ]₅ ([Γ] ∙ [Σ]) [A]₅
      [t] = IS.irrelevanceTerm {t = t} [Γ]₆ [Γ] [Σ]₆ [Σ] [t]₆
      [u] = IS.irrelevanceTerm {A = A₊} {u} [Γ]₇ ([Γ] ∙ [F] ∙ [G]) [A₊]₇ [A₊] [u]₇
      ⊩ʳu′ = irrelevance {t = u} [Γ]₂ ([Γ] ∙ [F] ∙ [G]) [A₊]₂ [A₊] ⊩ʳu
      r≡𝟘→k≡0 = case no-erased-matches of λ where
        (inj₁ nem) → λ r≡𝟘 → PE.⊥-elim (nem 𝟙≉𝟘 P r≡𝟘)
        (inj₂ k≡0) → λ _ → k≡0
      [At] , ⊩ʳprodrec =
        prodrecʳ [Γ] [F] [G] [Σ] [A] [A₊] [t] [u]
                 (λ r≢𝟘 → PE.subst (δ ▸ _ ⊩ʳ⟨ _ ⟩ t ∷[_] _ / _ / [Σ]) (≉𝟘→ᵐ·≡ r≢𝟘) ⊩ʳt)
                 ⊩ʳu′ r≡𝟘→k≡0
  in  [Γ] , [At] ,
      subsumption-≤ {t = prodrec _ _ _ A t u} [Γ] [At] ⊩ʳprodrec γ≤pδ+η
fundamental (zeroⱼ ⊢Γ) γ▸t = zeroʳ ⊢Γ
fundamental (sucⱼ {n = t} Γ⊢t:ℕ) γ▸t =
  let invUsageSuc δ▸t γ≤δ = inv-usage-suc γ▸t
      [Γ] , [ℕ] , ⊩ʳt = fundamental Γ⊢t:ℕ δ▸t
      δ⊩ʳsuct = sucʳ [Γ] [ℕ] ⊩ʳt Γ⊢t:ℕ
      γ⊩ʳsuct = subsumption-≤ {A = ℕ} {t = suc t} [Γ] [ℕ] δ⊩ʳsuct γ≤δ
  in  [Γ] , [ℕ] , γ⊩ʳsuct
fundamental (natrecⱼ {p = p} {q = q} {r = r} {G = A} {s = s} {z = z} {n = n} Γ⊢A Γ⊢z:A Γ⊢s:A Γ⊢n:ℕ) γ▸t =
  let invUsageNatrec δ▸z η▸s θ▸n _ γ≤γ′ = inv-usage-natrec γ▸t
      [Γ]   , [A₀]  , ⊩ʳz  = fundamental Γ⊢z:A δ▸z
      [ΓℕA] , [A₊]′ , ⊩ʳs′ = fundamental Γ⊢s:A η▸s
      [Γ]′  , [ℕ]′  , ⊩ʳn′ = fundamental Γ⊢n:ℕ θ▸n
      [ℕ] = ℕᵛ {l = ¹} [Γ]
      [Γℕ] = [Γ] ∙ [ℕ]
      [Γℕ]′ , [A]′ = F.fundamental Γ⊢A
      [A] = IS.irrelevance {A = A} [Γℕ]′ [Γℕ] [A]′
      [A₊] = IS.irrelevance {A = wk1 (A [ (suc (var x0)) ]↑)}
                            [ΓℕA] ([Γℕ] ∙ [A]) [A₊]′
      [Γ]ᶻ , [A]ᶻ , [z]′ = F.fundamentalTerm Γ⊢z:A
      [z] = IS.irrelevanceTerm {A = A [ zero ]} {t = z} [Γ]ᶻ [Γ] [A]ᶻ [A₀] [z]′
      [Γ]ˢ , [A]ˢ , [s]′ = F.fundamentalTerm Γ⊢s:A
      [s] = IS.irrelevanceTerm {A = wk1 (A [ (suc (var x0)) ]↑)} {t = s}
                               [Γ]ˢ ([Γℕ] ∙ [A]) [A]ˢ [A₊] [s]′
      [Γ]ⁿ , [ℕ]ⁿ , [n]′ = F.fundamentalTerm Γ⊢n:ℕ
      [n] = IS.irrelevanceTerm {A = ℕ} {t = n} [Γ]ⁿ [Γ] [ℕ]ⁿ [ℕ] [n]′
      ⊩ʳs = irrelevance {A = wk1 (A [ (suc (var x0)) ]↑)} {t = s}
                        [ΓℕA] ([Γℕ] ∙ [A]) [A₊]′ [A₊] ⊩ʳs′
      ⊩ʳn = irrelevance {A = ℕ} {t = n} [Γ]′ [Γ] [ℕ]′ [ℕ] ⊩ʳn′
      [A[n]] , ⊩ʳnatrec = natrecʳ {A = A} {z = z} {s = s} {m = n}
                                  [Γ] [A] [A₊] [A₀] [z] [s] [n] ⊩ʳz ⊩ʳs ⊩ʳn
  in  [Γ] , [A[n]] , subsumption-≤ {A = A [ n ]} {t = natrec p q r A z s n}
                                   [Γ] [A[n]] ⊩ʳnatrec γ≤γ′
fundamental {Γ = Γ} {γ = γ} (Emptyrecⱼ {p = p} {A = A} {e = t} ⊢A Γ⊢t:Empty) γ▸t =
  let invUsageEmptyrec δ▸t _ γ≤δ = inv-usage-Emptyrec γ▸t
      [Γ] , [Empty] , ⊩ʳt = fundamental Γ⊢t:Empty δ▸t
      [Γ]′ , [A]′ = F.fundamental ⊢A
      [A] = IS.irrelevance {A = A} [Γ]′ [Γ] [A]′
      [Γ]″ , [Empty]′ , [t]′ = F.fundamentalTerm Γ⊢t:Empty
      [t] = IS.irrelevanceTerm {A = Empty} {t = t} [Γ]″ [Γ] [Empty]′ [Empty] [t]′
      γ⊩ʳEmptyrec = Emptyrecʳ {A = A} {t = t} {p = p} [Γ] [Empty] [A] [t]
  in  [Γ] , [A] , γ⊩ʳEmptyrec
fundamental (starⱼ ⊢Γ ok) _ = starʳ ⊢Γ ok
fundamental (conv {t = t} {A = A} {B = B} Γ⊢t:A A≡B) γ▸t =
  let [Γ] , [A] , ⊩ʳt = fundamental Γ⊢t:A γ▸t
      Γ⊢B = syntacticTerm (conv Γ⊢t:A A≡B)
      [Γ]′ , [B]′ = F.fundamental Γ⊢B
      [B] = IS.irrelevance {A = B} [Γ]′ [Γ] [B]′
  in  [Γ] , [B] , convʳ {A = A} {B = B} {t = t} [Γ] [A] [B] A≡B ⊩ʳt

-- Fundamental lemma for fully erased terms

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
  [id] = IS.irrelevanceSubst [Δ] [Δ] ⊢Δ′ ⊢Δ [id]′
  [idA] = proj₁ (unwrap [A] {σ = idSubst} ⊢Δ [id])
  [A]′ = I.irrelevance′ (subst-id A) [idA]

  lemma :
    ∀ m →
    𝟘ᶜ ▸ Δ ⊩ʳ⟨ ¹ ⟩ t ∷[ m ] A / [Δ] / [A] →
    t ®⟨ ¹ ⟩ erase t ∷ A ◂ ⌜ m ⌝ / [A]′
  lemma 𝟘ᵐ with is-𝟘? 𝟘
  ... | yes 𝟘≡𝟘 = _
  ... | no 𝟘≢𝟘 = PE.⊥-elim (𝟘≢𝟘 PE.refl)

  lemma 𝟙ᵐ ⊩ʳt with is-𝟘? 𝟙
  ... | yes 𝟙≡𝟘 = ⊥-elim (𝟙≉𝟘 𝟙≡𝟘)
  ... | no 𝟙≢𝟘 =
    PE.subst₂ (λ x y → x ®⟨ ¹ ⟩ y ∷ A / [A]′)
      (subst-id t) (TP.subst-id (erase t)) t®t″
    where
    id®id′ = erasedSubst {l = ¹} {σ′ = T.idSubst} [Δ] [id]
    t®t′ = ⊩ʳt [id] id®id′
    t®t″ = irrelevanceTerm′ (subst-id A) [idA] [A]′ t®t′
