{-# OPTIONS --without-K --allow-unsolved-metas #-}
open import Definition.Modality.Erasure

open import Definition.Typed.EqualityRelation


module Erasure.LogicalRelation.Fundamental {{eqrel : EqRelSet Erasure}} where
open EqRelSet {{...}}

open import Definition.LogicalRelation Erasure
import Definition.LogicalRelation.Fundamental Erasure as F
open import Definition.LogicalRelation.Fundamental.Reducibility Erasure
import Definition.LogicalRelation.Irrelevance Erasure as I
open import Definition.LogicalRelation.Properties.Escape Erasure
open import Definition.LogicalRelation.Substitution Erasure
open import Definition.LogicalRelation.Substitution.Conversion Erasure
open import Definition.LogicalRelation.Substitution.Escape Erasure
open import Definition.LogicalRelation.Substitution.MaybeEmbed Erasure
open import Definition.LogicalRelation.Substitution.Properties Erasure
open import Definition.LogicalRelation.Substitution.Weakening Erasure
import Definition.LogicalRelation.Substitution.Irrelevance Erasure as IS
open import Definition.LogicalRelation.Substitution.Introductions.Universe Erasure
open import Definition.LogicalRelation.Substitution.Introductions.Pi Erasure
open import Definition.LogicalRelation.Substitution.Introductions.Nat Erasure

open import Definition.Modality.Context ErasureModality
open import Definition.Modality.Erasure.Properties
open import Definition.Modality.Usage ErasureModality
open import Definition.Modality.Usage.Inversion ErasureModality

open import Definition.Untyped Erasure hiding (_∷_)
open import Definition.Untyped.Properties Erasure
open import Definition.Typed Erasure
open import Definition.Typed.Consequences.Substitution Erasure
open import Definition.Typed.Consequences.Syntactic Erasure

-- open import Erasure.Extraction
open import Erasure.LogicalRelation
open import Erasure.LogicalRelation.Conversion
open import Erasure.LogicalRelation.Fundamental.Application
open import Erasure.LogicalRelation.Fundamental.Empty
open import Erasure.LogicalRelation.Fundamental.Lambda
open import Erasure.LogicalRelation.Fundamental.Nat
open import Erasure.LogicalRelation.Fundamental.Natrec
open import Erasure.LogicalRelation.Fundamental.Product
open import Erasure.LogicalRelation.Fundamental.Unit

open import Erasure.LogicalRelation.Irrelevance
-- open import Erasure.LogicalRelation.Irrelevance
open import Erasure.LogicalRelation.Properties
import Erasure.Target as T
open import Erasure.Extraction
import Erasure.Target.Properties as TP

open import Tools.Fin
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Unit

private
  variable
     n : Nat
     Γ : Con Term n
     t A u : Term n
     B : Term (1+ n)
     -- w : T.Term n
     γ : Conₘ n
     p q : Erasure
     σ : Subst 0 n
     x : Fin n
     σ′ : T.Subst 0 n


fundamentalVar′ : ([Γ] : ⊩ᵛ Γ)
               → x ∷ A ∈ Γ
               → x ◂ ω ∈ γ
               → ([σ] : ε ⊩ˢ σ ∷ Γ / [Γ] / ε)
               → (σ®σ′ : σ ®⟨ ¹ ⟩ σ′ ∷ Γ ◂ γ / [Γ] / [σ])
               → ∃ λ ([A] : Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ])
               → σ x ®⟨ ¹ ⟩ σ′ x ∷ subst σ A / proj₁ ([A] ε [σ])
fundamentalVar′ ε ()
fundamentalVar′ {σ = σ} (_∙_ {A = A} [Γ] [A]) here here
                ([tailσ] , [headσ]) (σ®σ′ , σ0®σ′0) =
  let [A]′ = proj₁ ([A] ε [tailσ])
      [↑A] = wk1ᵛ {A = A} {F = A} [Γ] [A] [A]
      [↑A]′ = maybeEmbᵛ {A = wk1 A} (_∙_ {A = A} [Γ] [A]) [↑A]
      [σ↑A] = proj₁ ([↑A]′ {σ = σ} ε ([tailσ] , [headσ]))
      A≡A : ε ⊢ subst (tail σ) A ≡ subst (tail σ) A
      A≡A = refl (escape [A]′)
      A≡A′ = PE.subst (ε ⊢ subst (tail σ) A ≡_)
                      (PE.sym (wk1-tail A)) A≡A
  in  [↑A]′ , convTermʳ [A]′ [σ↑A] A≡A′ σ0®σ′0
fundamentalVar′ (_∙_ {A = A} [Γ] [A]) (there {A = B} x) (there x₁)
                ([tailσ] , [headσ]) (σ®σ′ , σ0®σ′0) =
  let [σA] = proj₁ ([A] ε [tailσ])
      [A]′ = maybeEmbᵛ {A = A} [Γ] [A]
      [B] , t®v = fundamentalVar′ [Γ] x x₁ [tailσ] σ®σ′
      [↑B] = wk1ᵛ {A = B} {F = A} [Γ] [A]′ [B]
      [↑B]′ = maybeEmbᵛ {A = wk1 B} (_∙_ {A = A} [Γ] [A]′) [↑B]
      [↑B]″ = IS.irrelevance {A = wk1 B} (_∙_ {A = A} [Γ] [A]′) ([Γ] ∙ [A]) [↑B]′
      t®v′ = irrelevanceTerm′ (PE.sym (wk1-tail B)) (proj₁ ([B] ε [tailσ]))
                              (proj₁ ([↑B]″ ε ([tailσ] , [headσ]))) t®v
  in  [↑B]″ , t®v′

fundamentalVar : ([Γ] : ⊩ᵛ Γ)
               → x ∷ A ∈ Γ
               → γ ▸ var x
               → ∃ λ ([A] : Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ])
               → γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ var x ∷ A / [Γ] / [A]
fundamentalVar {γ = γ} [Γ] x∷A∈Γ γ▸x =
  let [A] , _ = F.fundamentalVar x∷A∈Γ [Γ]
      x◂ω∈γ = valid-var-usage γ▸x
  in [A] , λ [σ] σ®σ′ →
     let [A]′ , t®v = fundamentalVar′ [Γ] x∷A∈Γ x◂ω∈γ [σ] σ®σ′
     in  irrelevanceTerm (proj₁ ([A]′ ε [σ])) (proj₁ ([A] ε [σ])) t®v



fundamental : Γ ⊢ t ∷ A → γ ▸ t
            → ∃ λ ([Γ] : ⊩ᵛ Γ)
            → ∃ λ ([A] : Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ])
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
  in  [Γ] , [G[u]] , subsumption {t = t ∘ p ▷ u} {A = G [ u ]} [Γ] [G[u]] ⊩ʳt∘u γ≤δ+pη
fundamental (prodⱼ {F = F} {G = G} {t = t} {u = u} Γ⊢F Γ⊢G Γ⊢t:F Γ⊢u:G) γ▸t =
  let invUsageProd δ▸t η▸u γ′≡δ+η γ≤δ+η = inv-usage-prod γ▸t
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
  in  [Γ] , [Σ] , subsumption {t = prod t u} {A = Σ _ ▷ F ▹ G}
                              [Γ] [Σ] ⊩ʳp (PE.subst₂ _≤ᶜ_ PE.refl γ′≡δ+η γ≤δ+η)
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
fundamental (prodrecⱼ Γ⊢F Γ⊢G Γ⊢t:Σ Γ⊢A Γ⊢u:A) γ▸t =
  let invUsageProdrec δ▸t η▸u le = inv-usage-prodrec γ▸t
      [Γ] , [Σ] , ⊩ʳt = fundamental Γ⊢t:Σ δ▸t
      [ΓFG] , [A] , ⊩ʳu = fundamental Γ⊢u:A η▸u
  in  [Γ] , ({!!} , {!⊩ʳu!})
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
  in  [Γ] , [A[n]] , {!subsumption {t = natrec p r A z s n} {A = A [ n ]}
                                 [Γ] [A[n]] ⊩ʳnatrec γ≤γ′!}
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


fundamental′ : ∀ {t A} → ε ⊢ t ∷ A → ε ▸ t
             → ∃ λ ([A] : ε ⊩⟨ ¹ ⟩ A)
             → t ®⟨ ¹ ⟩ erase t ∷ A / [A]
fundamental′ {t = t} {A = A} ε⊢t∷A ε▸t =
  let [ε] , [A] , ⊩ʳt = fundamental ε⊢t∷A ε▸t
      [A]′ = IS.irrelevance {A = A} [ε] ε [A]
      [σA] = proj₁ ([A]′ {σ = idSubst} ε (idSubstS  ε))
      [σA]′ = I.irrelevance′ (subst-id A) [σA]
      ⊩ʳt′ = irrelevance {A = A} {t = t} [ε] ε [A] [A]′ ⊩ʳt
      t®v = ⊩ʳt′ {σ′ = T.idSubst} (idSubstS ε) tt
      t®v′ = irrelevanceTerm′ (subst-id A) [σA] [σA]′ t®v
      t®v″ = PE.subst₂ (λ t′ v′ → t′ ®⟨ _ ⟩ v′ ∷ A / [σA]′) (subst-id t) (TP.subst-id (erase t)) t®v′
  in  [σA]′ , t®v″
