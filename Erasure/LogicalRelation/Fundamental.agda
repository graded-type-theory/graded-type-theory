{-# OPTIONS --without-K --safe #-}

open import Definition.Modality.Instances.Erasure
open import Definition.Typed.EqualityRelation
open import Definition.Untyped Erasure hiding (_∷_)
open import Definition.Typed Erasure′
open import Tools.Empty

module Erasure.LogicalRelation.Fundamental {k} {Δ : Con Term k} (⊢Δ : ⊢ Δ)
                                           (consistent : ∀ {t} → Δ ⊢ t ∷ Empty → ⊥)
                                           {{eqrel : EqRelSet Erasure′}} where
open EqRelSet {{...}}

open import Definition.LogicalRelation Erasure′
open import Definition.LogicalRelation.Properties.Escape Erasure′
open import Definition.LogicalRelation.Substitution Erasure′
open import Definition.LogicalRelation.Substitution.MaybeEmbed Erasure′
open import Definition.LogicalRelation.Substitution.Properties Erasure′
open import Definition.LogicalRelation.Substitution.Weakening Erasure′
open import Definition.LogicalRelation.Substitution.Introductions.Pi Erasure′
open import Definition.LogicalRelation.Substitution.Introductions.Nat Erasure′

import Definition.LogicalRelation.Fundamental Erasure′ as F
import Definition.LogicalRelation.Irrelevance Erasure′ as I
import Definition.LogicalRelation.Substitution.Irrelevance Erasure′ as IS

open import Definition.Modality.Instances.Erasure.Modality NoErasedMatching
open import Definition.Modality.Context ErasureModality
open import Definition.Modality.Instances.Erasure.Properties NoErasedMatching
open import Definition.Modality.Usage ErasureModality
open import Definition.Modality.Usage.Inversion ErasureModality

open import Definition.Untyped.Properties Erasure
open import Definition.Typed.Consequences.Syntactic Erasure′

open import Erasure.LogicalRelation ⊢Δ NoErasedMatching
open import Erasure.LogicalRelation.Conversion ⊢Δ NoErasedMatching
open import Erasure.LogicalRelation.Fundamental.Application ⊢Δ NoErasedMatching
open import Erasure.LogicalRelation.Fundamental.Empty ⊢Δ consistent NoErasedMatching
open import Erasure.LogicalRelation.Fundamental.Lambda ⊢Δ NoErasedMatching
open import Erasure.LogicalRelation.Fundamental.Nat ⊢Δ NoErasedMatching
open import Erasure.LogicalRelation.Fundamental.Natrec ⊢Δ NoErasedMatching
open import Erasure.LogicalRelation.Fundamental.Prodrec ⊢Δ NoErasedMatching
open import Erasure.LogicalRelation.Fundamental.Product ⊢Δ NoErasedMatching
open import Erasure.LogicalRelation.Fundamental.Unit ⊢Δ NoErasedMatching
open import Erasure.LogicalRelation.Irrelevance ⊢Δ NoErasedMatching
open import Erasure.LogicalRelation.Subsumption ⊢Δ NoErasedMatching

import Erasure.Target as T
open import Erasure.Extraction
import Erasure.Target.Properties as TP

open import Tools.Fin
open import Tools.Level
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
     m n : Nat
     Γ : Con Term n
     t u A B : Term n
     γ : Conₘ n
     p q : Erasure
     σ : Subst m n
     x : Fin n
     σ′ : T.Subst m n

-- Fundamental lemma for variables

fundamentalVar′ : ([Γ] : ⊩ᵛ Γ)
                → x ∷ A ∈ Γ
                → x ◂ ω ∈ γ
                → ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
                → (σ®σ′ : σ ®⟨ ¹ ⟩ σ′ ∷ Γ ◂ γ / [Γ] / [σ])
                → ∃ λ ([A] : Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ]) → σ x ®⟨ ¹ ⟩ σ′ x ∷ subst σ A / proj₁ (unwrap [A] ⊢Δ [σ])
fundamentalVar′ ε ()
fundamentalVar′ {σ = σ} (_∙_ {A = A} [Γ] [A]) here here
                ([tailσ] , [headσ]) (σ®σ′ , σ0®σ′0) =
  let [A]′ = proj₁ (unwrap [A] ⊢Δ [tailσ])
      [↑A] = wk1ᵛ {A = A} {F = A} [Γ] [A] [A]
      [↑A]′ = maybeEmbᵛ {A = wk1 A} (_∙_ {A = A} [Γ] [A]) [↑A]
      [σ↑A] = proj₁ (unwrap [↑A]′ {σ = σ} ⊢Δ ([tailσ] , [headσ]))
      A≡A : Δ ⊢ subst (tail σ) A ≡ subst (tail σ) A
      A≡A = refl (escape [A]′)
      A≡A′ = PE.subst (Δ ⊢ subst (tail σ) A ≡_)
                      (PE.sym (wk1-tail A)) A≡A
  in  [↑A]′ , convTermʳ [A]′ [σ↑A] A≡A′ σ0®σ′0
fundamentalVar′ (_∙_ {A = A} [Γ] [A]) (there {A = B} x) (there x₁)
                ([tailσ] , [headσ]) (σ®σ′ , σ0®σ′0) =
  let [σA] = proj₁ (unwrap [A] ⊢Δ [tailσ])
      [A]′ = maybeEmbᵛ {A = A} [Γ] [A]
      [B] , t®v = fundamentalVar′ [Γ] x x₁ [tailσ] σ®σ′
      [↑B] = wk1ᵛ {A = B} {F = A} [Γ] [A]′ [B]
      [↑B]′ = maybeEmbᵛ {A = wk1 B} (_∙_ {A = A} [Γ] [A]′) [↑B]
      [↑B]″ = IS.irrelevance {A = wk1 B} (_∙_ {A = A} [Γ] [A]′) ([Γ] ∙ [A]) [↑B]′
      t®v′ = irrelevanceTerm′ (PE.sym (wk1-tail B)) (proj₁ (unwrap [B] ⊢Δ [tailσ]))
                              (proj₁ (unwrap [↑B]″ ⊢Δ ([tailσ] , [headσ]))) t®v
  in  [↑B]″ , t®v′

fundamentalVar : ([Γ] : ⊩ᵛ Γ)
               → x ∷ A ∈ Γ
               → γ ▸ var x
               → ∃ λ ([A] : Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ]) → γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ var x ∷ A / [Γ] / [A]
fundamentalVar {γ = γ} [Γ] x∷A∈Γ γ▸x =
  let [A] , _ = F.fundamentalVar x∷A∈Γ [Γ]
      x◂ω∈γ = valid-var-usage γ▸x
  in [A] , λ [σ] σ®σ′ →
     let [A]′ , t®v = fundamentalVar′ [Γ] x∷A∈Γ x◂ω∈γ [σ] σ®σ′
     in  irrelevanceTerm (proj₁ (unwrap [A]′ ⊢Δ [σ])) (proj₁ (unwrap [A] ⊢Δ [σ])) t®v

-- Fundamental lemma for the erasure relation
-- Does not allow matching on erased pairs

fundamental : Γ ⊢ t ∷ A → γ ▸ t
            → ∃₂ λ ([Γ] : ⊩ᵛ Γ) ([A] : Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ])
                 → γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ t ∷ A / [Γ] / [A]
fundamental Γ⊢Π@(Πⱼ Γ⊢F:U ▹ Γ⊢G:U) γ▸t =
  let invUsageΠΣ δ▸F _ _ = inv-usage-Π γ▸t
      [Γ] , _ , _ = fundamental Γ⊢F:U δ▸F
      [U] , ⊩ʳΠ = Πʳ [Γ] Γ⊢Π
  in  [Γ] , [U] , ⊩ʳΠ
fundamental Γ⊢Σ@(Σⱼ Γ⊢F:U ▹ Γ⊢G:U) γ▸t =
  let invUsageΠΣ δ▸F _ _ = inv-usage-Σ γ▸t
      [Γ] , _ , _ = fundamental Γ⊢F:U δ▸F
      [U] , ⊩ʳΣ = Σʳ [Γ] Γ⊢Σ
  in  [Γ] , [U] , ⊩ʳΣ
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
  let invUsageProdᵣ δ▸t η▸u γ≤δ+η = inv-usage-prodₑ γ▸t
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
  in  [Γ] , [Σ] , subsumption {t = prod! t u} {A = Σ _ ▷ F ▹ G}
                              [Γ] [Σ] ⊩ʳp γ≤δ+η
fundamental (fstⱼ {F = F} {t = t} Γ⊢F Γ⊢G Γ⊢t:Σ) γ▸t =
  let invUsageProj δ▸t δ≤𝟘 = inv-usage-fst γ▸t
      [Γ] , [Σ] , ⊩ʳt = fundamental Γ⊢t:Σ δ▸t
      [F] , ⊩ʳt₁ = fstʳ Γ⊢F Γ⊢G Γ⊢t:Σ [Γ] [Σ] ⊩ʳt
  in  [Γ] , [F] , subsumption {t = fst t} {A = F} [Γ] [F] ⊩ʳt₁ δ≤𝟘
fundamental (sndⱼ {G = G} {t = t} Γ⊢F Γ⊢G Γ⊢t:Σ) γ▸t =
  let invUsageProj δ▸t δ≤𝟘 = inv-usage-snd γ▸t
      [Γ] , [Σ] , ⊩ʳt = fundamental Γ⊢t:Σ δ▸t
      [G] , ⊩ʳt₂ = sndʳ Γ⊢F Γ⊢G Γ⊢t:Σ [Γ] [Σ] ⊩ʳt
  in  [Γ] , [G] , subsumption {t = snd t} {A = G [ fst t ]} [Γ] [G] ⊩ʳt₂ δ≤𝟘
fundamental (prodrecⱼ {p = 𝟘} {t = t} {u} {F} {G} {A} Γ⊢F Γ⊢G Γ⊢A Γ⊢t Γ⊢u) γ▸prodrec
  with inv-usage-prodrec γ▸prodrec
... | invUsageProdrec _ _ _ () _
fundamental (prodrecⱼ {p = ω} {q′ = q′} {t = t} {u} {F} {G} {A} Γ⊢F Γ⊢G Γ⊢A Γ⊢t Γ⊢u) γ▸prodrec =
  let invUsageProdrec δ▸t η▸u _ P γ≤pδ+η = inv-usage-prodrec γ▸prodrec
      [Γ] , [Σ] , ⊩ʳt = fundamental Γ⊢t δ▸t
      [Γ]₂ , [A₊]₂ , ⊩ʳu = fundamental Γ⊢u η▸u
      [Γ]₃ , [F]₃ = F.fundamental Γ⊢F
      [Γ]₄ , [G]₄ = F.fundamental Γ⊢G
      [Γ]₅ , [A]₅ = F.fundamental Γ⊢A
      [Γ]₆ , [Σ]₆ , [t]₆ = F.fundamentalTerm Γ⊢t
      [Γ]₇ , [A₊]₇ , [u]₇ = F.fundamentalTerm Γ⊢u
      A₊ = A [ prodᵣ (var (x0 +1)) (var x0) ]↑²
      [F] = IS.irrelevance {A = F} [Γ]₃ [Γ] [F]₃
      [G] = IS.irrelevance {A = G} [Γ]₄ ([Γ] ∙ [F]) [G]₄
      [A₊] = IS.irrelevance {A = A₊} [Γ]₂ ([Γ] ∙ [F] ∙ [G]) [A₊]₂
      [A] = IS.irrelevance {A = A} [Γ]₅ ([Γ] ∙ [Σ]) [A]₅
      [t] = IS.irrelevanceTerm {A = Σ _ ▷ F ▹ G} {t} [Γ]₆ [Γ] [Σ]₆ [Σ] [t]₆
      [u] = IS.irrelevanceTerm {A = A₊} {u} [Γ]₇ ([Γ] ∙ [F] ∙ [G]) [A₊]₇ [A₊] [u]₇
      ⊩ʳu′ = irrelevance {A = A [ prodᵣ (var (x0 +1)) (var x0) ]↑²} {t = u}
                         [Γ]₂ ([Γ] ∙ [F] ∙ [G]) [A₊]₂ [A₊] ⊩ʳu
      [At] , ⊩ʳprodrec = prodrecωʳ {F = F} {G} {A = A} {t} {u} {q′ = q′}
                                   [Γ] [F] [G] [Σ] [A] [A₊] [t] [u] ⊩ʳt ⊩ʳu′
  in  [Γ] , [At] , subsumption {t = prodrec _ _ A t u} {A = A [ t ]} [Γ] [At] ⊩ʳprodrec γ≤pδ+η
fundamental (zeroⱼ ⊢Γ) γ▸t = zeroʳ ⊢Γ
fundamental (sucⱼ {n = t} Γ⊢t:ℕ) γ▸t =
  let invUsageSuc δ▸t γ≤δ = inv-usage-suc γ▸t
      [Γ] , [ℕ] , ⊩ʳt = fundamental Γ⊢t:ℕ δ▸t
      δ⊩ʳsuct = sucʳ [Γ] [ℕ] ⊩ʳt Γ⊢t:ℕ
      γ⊩ʳsuct = subsumption {t = suc t} {A = ℕ} [Γ] [ℕ] δ⊩ʳsuct γ≤δ
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
  in  [Γ] , [A[n]] , subsumption {t = natrec p q r A z s n} {A = A [ n ]}
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
fundamental (starⱼ ⊢Γ) γ▸t = starʳ ⊢Γ
fundamental (conv {t = t} {A = A} {B = B} Γ⊢t:A A≡B) γ▸t =
  let [Γ] , [A] , ⊩ʳt = fundamental Γ⊢t:A γ▸t
      Γ⊢B = syntacticTerm (conv Γ⊢t:A A≡B)
      [Γ]′ , [B]′ = F.fundamental Γ⊢B
      [B] = IS.irrelevance {A = B} [Γ]′ [Γ] [B]′
  in  [Γ] , [B] , convʳ {A = A} {B = B} {t = t} [Γ] [A] [B] A≡B ⊩ʳt

-- Fundamental lemma for fully erased terms

fundamentalErased : Δ ⊢ t ∷ A
                  → 𝟘ᶜ ▸ t
                  → ∃ λ ([A] : Δ ⊩⟨ ¹ ⟩ A) → t ®⟨ ¹ ⟩ erase t ∷ A / [A]
fundamentalErased {t = t} {A = A} ⊢t 𝟘▸t =
  let [Δ] , [A] , ⊩ʳt = fundamental ⊢t 𝟘▸t
      [id]′ = idSubstS [Δ]
      ⊢Δ′ = soundContext [Δ]
      [id] = IS.irrelevanceSubst [Δ] [Δ] ⊢Δ′ ⊢Δ [id]′
      [idA] = proj₁ (unwrap [A] {σ = idSubst} ⊢Δ [id])
      [A]′ = I.irrelevance′ (subst-id A) [idA]
      id®id′ = erasedSubst {l = ¹} {σ′ = T.idSubst} [Δ] [id]
      t®t′ = ⊩ʳt [id] id®id′
      t®t″ = irrelevanceTerm′ (subst-id A) [idA] [A]′ t®t′
  in  [A]′ , PE.subst₂ (λ x y → x ®⟨ ¹ ⟩ y ∷ A / [A]′)
                       (subst-id t) (TP.subst-id (erase t)) t®t″
