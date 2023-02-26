open import Definition.Modality.Instances.Erasure
  using (Erasure; ω)
open import Definition.Modality.Restrictions
open import Definition.Typed.EqualityRelation

module Erasure.LogicalRelation.Fundamental
  (restrictions : Restrictions Erasure)
  {{eqrel : EqRelSet Erasure}}
  where

open EqRelSet {{...}}

open import Definition.LogicalRelation Erasure
open import Definition.LogicalRelation.Properties.Escape Erasure
open import Definition.LogicalRelation.Substitution Erasure
open import Definition.LogicalRelation.Substitution.MaybeEmbed Erasure
open import Definition.LogicalRelation.Substitution.Properties Erasure
open import Definition.LogicalRelation.Substitution.Weakening Erasure
open import Definition.LogicalRelation.Substitution.Introductions.Pi Erasure
open import Definition.LogicalRelation.Substitution.Introductions.Nat Erasure

import Definition.LogicalRelation.Fundamental Erasure as F
import Definition.LogicalRelation.Irrelevance Erasure as I
import Definition.LogicalRelation.Substitution.Irrelevance Erasure as IS

open import Definition.Modality.Instances.Erasure.Modality restrictions
open import Definition.Modality.Context ErasureModality
open import Definition.Modality.Instances.Erasure.Properties
  restrictions
open import Definition.Modality.Usage ErasureModality
open import Definition.Modality.Usage.Inversion ErasureModality
open import Definition.Modality.Usage.Properties ErasureModality
open import Definition.Mode ErasureModality

open import Definition.Untyped Erasure hiding (_∷_)
open import Definition.Untyped.Properties Erasure
open import Definition.Typed Erasure
open import Definition.Typed.Consequences.Syntactic Erasure

open import Erasure.LogicalRelation restrictions
open import Erasure.LogicalRelation.Conversion restrictions
open import Erasure.LogicalRelation.Fundamental.Application restrictions
open import Erasure.LogicalRelation.Fundamental.Empty restrictions
open import Erasure.LogicalRelation.Fundamental.Lambda restrictions
open import Erasure.LogicalRelation.Fundamental.Nat restrictions
open import Erasure.LogicalRelation.Fundamental.Natrec restrictions
open import Erasure.LogicalRelation.Fundamental.Product restrictions
open import Erasure.LogicalRelation.Fundamental.Unit restrictions
open import Erasure.LogicalRelation.Irrelevance restrictions
open import Erasure.LogicalRelation.Subsumption restrictions

import Erasure.Target as T
open import Erasure.Extraction
import Erasure.Target.Properties as TP

open import Tools.Fin
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PartialOrder
open import Tools.Relation
open import Tools.Unit

open Modality ErasureModality

private
  variable
     n : Nat
     Γ : Con Term n
     t A u : Term n
     B : Term (1+ n)
     γ : Conₘ n
     p q : Erasure
     σ : Subst 0 n
     x : Fin n
     σ′ : T.Subst 0 n
     m : Mode
     s : SigmaMode

inv-usage-prodₑ : γ ▸[ m ] prod s p t u → InvUsageProdᵣ γ m p t u
inv-usage-prodₑ {γ = γ} {s = Σₚ} {p = p} γ▸t with inv-usage-prodₚ γ▸t
... | invUsageProdₚ {δ = δ} {η = η} δ▸t η▸u γ≤pδ∧η =
  invUsageProdᵣ δ▸t η▸u PE.refl
    (begin
       γ            ≤⟨ γ≤pδ∧η ⟩
       p ·ᶜ δ ∧ᶜ η  ≈⟨ ∧ᶜ≈ᶜ+ᶜ ⟩
       p ·ᶜ δ +ᶜ η  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
inv-usage-prodₑ {s = Σᵣ} γ▸t = inv-usage-prodᵣ γ▸t

fundamentalVar′ : ([Γ] : ⊩ᵛ Γ)
               → x ∷ A ∈ Γ
               → x ◂ ω ∈ γ
               → ([σ] : ε ⊩ˢ σ ∷ Γ / [Γ] / ε)
               → (σ®σ′ : σ ®⟨ ¹ ⟩ σ′ ∷[ 𝟙ᵐ ] Γ ◂ γ / [Γ] / [σ])
               → ∃ λ ([A] : Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ])
               → σ x ®⟨ ¹ ⟩ σ′ x ∷ subst σ A / proj₁ (unwrap [A] ε [σ])
fundamentalVar′ ε ()
fundamentalVar′ {σ = σ} (_∙_ {A = A} [Γ] [A]) here here
                ([tailσ] , [headσ]) (σ®σ′ , σ0®σ′0) =
  let [A]′ = proj₁ (unwrap [A] ε [tailσ])
      [↑A] = wk1ᵛ {A = A} {F = A} [Γ] [A] [A]
      [↑A]′ = maybeEmbᵛ {A = wk1 A} (_∙_ {A = A} [Γ] [A]) [↑A]
      [σ↑A] = proj₁ (unwrap [↑A]′ {σ = σ} ε ([tailσ] , [headσ]))
      A≡A : ε ⊢ subst (tail σ) A ≡ subst (tail σ) A
      A≡A = refl (escape [A]′)
      A≡A′ = PE.subst (ε ⊢ subst (tail σ) A ≡_)
                      (PE.sym (wk1-tail A)) A≡A
  in  [↑A]′ , convTermʳ _ [A]′ [σ↑A] A≡A′ σ0®σ′0
fundamentalVar′ (_∙_ {A = A} [Γ] [A]) (there {A = B} x) (there x₁)
                ([tailσ] , [headσ]) (σ®σ′ , σ0®σ′0) =
  let [σA] = proj₁ (unwrap [A] ε [tailσ])
      [A]′ = maybeEmbᵛ {A = A} [Γ] [A]
      [B] , t®v = fundamentalVar′ [Γ] x x₁ [tailσ] σ®σ′
      [↑B] = wk1ᵛ {A = B} {F = A} [Γ] [A]′ [B]
      [↑B]′ = maybeEmbᵛ {A = wk1 B} (_∙_ {A = A} [Γ] [A]′) [↑B]
      [↑B]″ = IS.irrelevance {A = wk1 B} (_∙_ {A = A} [Γ] [A]′) ([Γ] ∙ [A]) [↑B]′
      t®v′ = irrelevanceTerm′ (PE.sym (wk1-tail B)) (proj₁ (unwrap [B] ε [tailσ]))
                              (proj₁ (unwrap [↑B]″ ε ([tailσ] , [headσ]))) t®v
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
  lemma 𝟘ᵐ = _

  lemma 𝟙ᵐ γ▸x [σ] σ®σ′ =
     let x◂ω∈γ = valid-var-usage γ▸x
         [A]′ , t®v = fundamentalVar′ [Γ] x∷A∈Γ x◂ω∈γ [σ] σ®σ′
     in  irrelevanceTerm (proj₁ (unwrap [A]′ ε [σ])) (proj₁ (unwrap [A] ε [σ])) t®v


fundamental : Γ ⊢ t ∷ A → γ ▸[ m ] t
            → ∃ λ ([Γ] : ⊩ᵛ Γ)
            → ∃ λ ([A] : Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ])
            → γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ t ∷[ m ] A / [Γ] / [A]
fundamental Γ⊢Π@(ΠΣⱼ Γ⊢F:U ▹ Γ⊢G:U) γ▸t =
  let invUsageΠΣ δ▸F _ _ = inv-usage-ΠΣ γ▸t
      [Γ] , _ , _ = fundamental Γ⊢F:U δ▸F
      [U] , ⊩ʳΠ = ΠΣʳ [Γ] Γ⊢Π
  in  [Γ] , [U] , ⊩ʳΠ
fundamental (ℕⱼ ⊢Γ) γ▸t = ℕʳ ⊢Γ
fundamental (Emptyⱼ ⊢Γ) γ▸t = Emptyʳ ⊢Γ
fundamental (Unitⱼ ⊢Γ) γ▸t = Unitʳ ⊢Γ
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
  in  [Γ] , [Π] , subsumption {t = lam p t} {A = Π p , q ▷ F ▹ G} [Γ] [Π] ⊩ʳλt δ≤γ
fundamental (_∘ⱼ_ {p = p} {q = q} {g = t} {a = u} {F = F} {G = G} Γ⊢t:Π Γ⊢u:F) γ▸t =
  let invUsageApp δ▸t η▸u γ≤δ+pη = inv-usage-app γ▸t
      [Γ]′ , [Π]′ , ⊩ʳt′ = fundamental Γ⊢t:Π δ▸t
      [Γ] , [F] , ⊩ʳu = fundamental Γ⊢u:F η▸u
      [Π] = IS.irrelevance {A = Π p , q ▷ F ▹ G} [Γ]′ [Γ] [Π]′
      ⊩ʳt = irrelevance {A = Π p , q ▷ F ▹ G} {t = t} [Γ]′ [Γ] [Π]′ [Π] ⊩ʳt′
      [Γ]″ , [F]′ , [u]′ = F.fundamentalTerm Γ⊢u:F
      [u] = IS.irrelevanceTerm {A = F} {t = u} [Γ]″ [Γ] [F]′ [F] [u]′
      [G[u]] , ⊩ʳt∘u = appʳ {F = F} {G = G} {u = u} {t = t} [Γ] [F] [Π] [u] ⊩ʳt ⊩ʳu
  in  [Γ] , [G[u]] , subsumption {t = t ∘⟨ p ⟩ u} {A = G [ u ]} [Γ] [G[u]] ⊩ʳt∘u γ≤δ+pη
fundamental (prodⱼ {F = F} {G = G} {t = t} {u = u} Γ⊢F Γ⊢G Γ⊢t:F Γ⊢u:G) γ▸t =
  let invUsageProdᵣ δ▸t η▸u γ′≡δ+η γ≤δ+η = inv-usage-prodₑ γ▸t
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
      [Σ] , ⊩ʳp = prodʳ {F = F} {G = G} {t = t} {u = u} [Γ] [F] [G] [G[t]] [t] [u] ⊩ʳt
                        (irrelevance {A = G [ t ]} {t = u} [Γ]₂ [Γ] [G[t]]′ [G[t]] ⊩ʳu)
  in  [Γ] , [Σ] ,
      subsumption {t = prod! t u} [Γ] [Σ] ⊩ʳp
        (PE.subst (_ ≤ᶜ_) γ′≡δ+η γ≤δ+η)
fundamental (fstⱼ {F = F} {t = t} Γ⊢F Γ⊢G Γ⊢t:Σ) γ▸t =
  let invUsageFst m′ m≡m′ᵐ·p δ▸t γ≤δ ok = inv-usage-fst γ▸t
      [Γ] , [Σ] , ⊩ʳt = fundamental Γ⊢t:Σ δ▸t
      [F] , ⊩ʳt₁ = fstʳ Γ⊢F Γ⊢G Γ⊢t:Σ [Γ] [Σ] ⊩ʳt
                     (fstₘ m′ (▸-cong m≡m′ᵐ·p δ▸t) (PE.sym m≡m′ᵐ·p) ok)
  in  [Γ] , [F] , subsumption {t = fst _ t} [Γ] [F] ⊩ʳt₁ γ≤δ
fundamental (sndⱼ {G = G} {t = t} Γ⊢F Γ⊢G Γ⊢t:Σ) γ▸t =
  let invUsageSnd δ▸t γ≤δ = inv-usage-snd γ▸t
      [Γ] , [Σ] , ⊩ʳt = fundamental Γ⊢t:Σ δ▸t
      [G] , ⊩ʳt₂ = sndʳ Γ⊢F Γ⊢G Γ⊢t:Σ [Γ] [Σ] ⊩ʳt
  in  [Γ] , [G] , subsumption {t = snd _ t} [Γ] [G] ⊩ʳt₂ γ≤δ
fundamental (prodrecⱼ {t = t} {u} {F} {G} {A} Γ⊢F Γ⊢G Γ⊢A Γ⊢t Γ⊢u) γ▸prodrec  =
  let invUsageProdrec δ▸t η▸u P γ≤pδ+η = inv-usage-prodrec γ▸prodrec
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
      [At] , ⊩ʳprodrec = prodrecʳ {F = F} {G} {A = A} {t} {u} [Γ] [F] [G] [Σ] [A] [A₊] [t] [u] ⊩ʳt ⊩ʳu′
  in  [Γ] , [At] ,
      subsumption {t = prodrec _ _ A t u} [Γ] [At] ⊩ʳprodrec γ≤pδ+η
fundamental (zeroⱼ ⊢Γ) γ▸t = zeroʳ ⊢Γ
fundamental (sucⱼ {n = t} Γ⊢t:ℕ) γ▸t =
  let invUsageSuc δ▸t γ≤δ = inv-usage-suc γ▸t
      [Γ] , [ℕ] , ⊩ʳt = fundamental Γ⊢t:ℕ δ▸t
      δ⊩ʳsuct = sucʳ [Γ] [ℕ] ⊩ʳt Γ⊢t:ℕ
      γ⊩ʳsuct = subsumption {t = suc t} {A = ℕ} [Γ] [ℕ] δ⊩ʳsuct γ≤δ
  in  [Γ] , [ℕ] , γ⊩ʳsuct
fundamental (natrecⱼ {p = p} {r = r} {G = A} {s = s} {z = z} {n = n} Γ⊢A Γ⊢z:A Γ⊢s:A Γ⊢n:ℕ) γ▸t =
  let invUsageNatrec δ▸z η▸s θ▸n γ≤γ′ = inv-usage-natrec γ▸t
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
  in  [Γ] , [A[n]] , subsumption {t = natrec p r A z s n} {A = A [ n ]}
                                 [Γ] [A[n]] ⊩ʳnatrec γ≤γ′
fundamental {Γ = Γ} {γ = γ} (Emptyrecⱼ {p = p} {A = A} {e = t} ⊢A Γ⊢t:Empty) γ▸t =
  let invUsageEmptyrec δ▸t γ≤δ = inv-usage-Emptyrec γ▸t
      [Γ] , [Empty] , ⊩ʳt = fundamental Γ⊢t:Empty δ▸t
      [Γ]′ , [A]′ = F.fundamental ⊢A
      [A] = IS.irrelevance {A = A} [Γ]′ [Γ] [A]′
      [Γ]″ , [Empty]′ , [t]′ = F.fundamentalTerm Γ⊢t:Empty
      [t] = IS.irrelevanceTerm {A = Empty} {t = t} [Γ]″ [Γ] [Empty]′ [Empty] [t]′
      γ⊩ʳEmptyrec = Emptyrecʳ {A = A} {t = t} {p = p} [Γ] [Empty] [A] [t]
  in  [Γ] , [A] , γ⊩ʳEmptyrec
fundamental (starⱼ ⊢Γ) γ▸t = starʳ ⊢Γ
fundamental (conv {t = t} {A = A} {B = B} Γ⊢t:A A≡B) γ▸t =
  let [Γ] , [A] , ⊩ʳt = fundamental Γ⊢t:A γ▸t
      Γ⊢B = syntacticTerm (conv Γ⊢t:A A≡B)
      [Γ]′ , [B]′ = F.fundamental Γ⊢B
      [B] = IS.irrelevance {A = B} [Γ]′ [Γ] [B]′
  in  [Γ] , [B] , convʳ {A = A} {B = B} {t = t} [Γ] [A] [B] A≡B ⊩ʳt


fundamental′ : ∀ {t A} → ε ⊢ t ∷ A → ε ▸[ m ] t
             → ∃ λ ([A] : ε ⊩⟨ ¹ ⟩ A)
             → t ®⟨ ¹ ⟩ erase t ∷ A ◂ ⌜ m ⌝ / [A]
fundamental′ {m = m} {t = t} {A = A} ε⊢t∷A ε▸t =
  [σA]′ , lemma m ⊩ʳt
  where
  [ε]-[A]-⊩ʳt = fundamental ε⊢t∷A ε▸t
  [ε] = [ε]-[A]-⊩ʳt .proj₁
  [A] = [ε]-[A]-⊩ʳt .proj₂ .proj₁
  ⊩ʳt = [ε]-[A]-⊩ʳt .proj₂ .proj₂
  [A]′ = IS.irrelevance [ε] ε [A]
  [σA] = proj₁ (unwrap [A]′ ε (idSubstS  ε))
  [σA]′ = I.irrelevance′ (subst-id A) [σA]

  lemma :
    ∀ m →
    ε ▸ ε ⊩ʳ⟨ ¹ ⟩ t ∷[ m ] A / [ε] / [A] →
    t ®⟨ ¹ ⟩ erase t ∷ A ◂ ⌜ m ⌝ / [σA]′
  lemma 𝟘ᵐ = _

  lemma 𝟙ᵐ ⊩ʳt =
    PE.subst₂ (λ t′ v′ → t′ ®⟨ _ ⟩ v′ ∷ A / [σA]′)
      (subst-id t) (TP.subst-id (erase t)) t®v′
    where
    ⊩ʳt′ = irrelevance {t = t} [ε] ε [A] [A]′ ⊩ʳt
    t®v = ⊩ʳt′ (idSubstS ε) tt
    t®v′ = irrelevanceTerm′ (subst-id A) [σA] [σA]′ t®v
