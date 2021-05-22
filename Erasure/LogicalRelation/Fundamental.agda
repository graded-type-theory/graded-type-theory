{-# OPTIONS --without-K  #-}
open import Definition.Modality.Erasure

open import Definition.Typed.EqualityRelation


module Erasure.LogicalRelation.Fundamental {{eqrel : EqRelSet Erasure}} where
open EqRelSet {{...}}

open import Definition.LogicalRelation Erasure
import Definition.LogicalRelation.Fundamental Erasure as F
import Definition.LogicalRelation.Irrelevance Erasure as I
-- open import Definition.LogicalRelation.Properties.Escape Erasure
-- open import Definition.LogicalRelation.ShapeView Erasure
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
open import Definition.Modality.Usage ErasureModality
open import Definition.Modality.Usage.Inversion ErasureModality

open import Definition.Untyped Erasure hiding (_∷_)
open import Definition.Untyped.Properties Erasure
open import Definition.Typed Erasure
open import Definition.Typed.Consequences.Substitution Erasure
open import Definition.Typed.Consequences.Syntactic Erasure

-- open import Erasure.Extraction
open import Erasure.LogicalRelation
open import Erasure.LogicalRelation.Fundamental.Application
open import Erasure.LogicalRelation.Fundamental.Empty
open import Erasure.LogicalRelation.Fundamental.Lambda
open import Erasure.LogicalRelation.Fundamental.Nat
open import Erasure.LogicalRelation.Fundamental.Product
open import Erasure.LogicalRelation.Fundamental.Unit

open import Erasure.LogicalRelation.Irrelevance
-- open import Erasure.LogicalRelation.Irrelevance
open import Erasure.LogicalRelation.Properties
import Erasure.Target as T
-- open import Erasure.Target.Properties as TP

open import Tools.Fin
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
     n : Nat
     Γ : Con Term n
     A u : Term n
     B t : Term (1+ n)
     -- w : T.Term n
     γ : Conₘ n
     p q : Erasure
     σ : Subst 0 n
     x : Fin n
     σ′ : T.Subst 0 n

lemma : ∀ {σ σ′ Γ γ [Γ] [σ] A p} → (x : Fin n) → σ ®⟨ ¹ ⟩ σ′ ∷ Γ ◂ γ / [Γ] / [σ]
                                   → x ∷ A ∈ Γ → x ◂ p ∈ γ
                                   → ∃ λ [A] → σ x ®⟨ ¹ ⟩ σ′ x ∷ subst σ A ◂ p / [A]
lemma {[Γ] = [Γ] ∙ [A]} {[σ] = [tailσ] , _} x0 (fst₂ , snd₂) here here = {!proj₁ ([A] ε [tailσ])!} , {!snd₂!}
lemma {[Γ] = _∙_ {A = A′} [Γ] [A]} {[σ] = [tailσ] , _} (_+1 x) (fst₁ , snd₁) (there {A = A} x∷A) (there x◂p) =
  let [A]′ , σx®σ′x = lemma x fst₁ x∷A x◂p
      [A]″ = I.irrelevance′ (PE.sym (wk1-tail A)) [A]′
  in  [A]″ ,  {![A]″!}
  -- irrelevanceTerm′ {!!} {![A]′!} {!!} σx®σ′x

-- fundamentalVar′ : ∀ ([Γ] : ⊩ᵛ Γ) ([σ] : ε ⊩ˢ σ ∷ Γ / [Γ] / ε)
--                 → x ∷ A ∈ Γ → x ◂ p ∈ γ
--                 → σ ®⟨ ¹ ⟩ σ′ ∷ Γ ◂ γ / [Γ] / [σ]
--                 → ∃ λ ([A] : Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ])
--                 → σ x ®⟨ ¹ ⟩ σ′ x ∷ subst σ A ◂ p / proj₁ ([A] ε [σ])
-- fundamentalVar′ (_∙_ {A = A} [Γ] [A]) ([tailσ] , ⊩σx0) here here (σ®σ′ , σx0®σ′x0) =
--   let [A]′ = wk1ᵛ {A = A} {F = A} [Γ] [A] [A]
--       [A]″ = maybeEmbᵛ ([Γ] ∙ [A]) [A]′
--       σx0®σ′x0′ = irrelevanceTerm′ (PE.sym (wk1-tail A)) {!!} {!!} σx0®σ′x0
--       -- (wk1-tail A) {![A]′!} (proj₁ ([A]′ ε {![tailσ]!})) σx0®σ′x0
--   in  [A]″ , {![A]″!}
-- fundamentalVar′ ([Γ] ∙ [B]) ([tailσ] , ⊩σx0) (there x∷A∈Γ) (there x◂p∈γ) (σ®σ′ , σx0®σ′x0) = {!x!}

-- fundamentalVar′ : ([Γ] : ⊩ᵛ Γ)
--                 → ([A] : Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ])
--                 → ([A]′ : Γ ∙ A ⊩ᵛ⟨ ¹ ⟩ wk1 A / [Γ] ∙ [A])
--                 → ([σ] : ε ⊩ˢ σ ∷ Γ ∙ A / [Γ] ∙ [A] / ε)
--                 → (σ®σ′ : σ ®⟨ ¹ ⟩ σ′ ∷ Γ ∙ A ◂ γ ∙ p / [Γ] ∙ [A] / [σ])
--                 → (x : Fin (1+ n))
--                 → σ x ®⟨ ¹ ⟩ σ′ x ∷ subst σ (wk1 A) / proj₁ ([A]′ ε [σ])
-- fundamentalVar′ [Γ] [A] [A]′ (fst₁ , snd₁) (fst₂ , snd₂) x = {!!}

-- fundamentalVar : x ∷ A ∈ Γ
--                → x ◂ p ∈ γ
--                → ([Γ] : ⊩ᵛ Γ)
--                → ∃ λ ([A] : Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ])
--                → γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ var x ∷ A / [Γ] / [A]
-- fundamentalVar here here (_∙_ {A = A} {l = l} [Γ] [A]) =
--   let [A]′ = wk1ᵛ {A = A} {F = A} [Γ] [A] [A]
--       [A]″ = maybeEmbᵛ {A = wk1 A} (_∙_ {A = A} [Γ] [A]) [A]′
--   in  [A]″ , λ {σ = σ} {σ′ = σ′} [σ] σ®σ′ →
--       let σx®σ′x = fundamentalVar′ {A = A} {σ = σ} {σ′ = σ′} {p = {!p!}} [Γ] (maybeEmbᵛ {A = {!A!}} [Γ] [A]) {![A]″!} [σ] σ®σ′ x0
--       in  {!!}
-- fundamentalVar (there x∷A∈Γ) (there x◂p∈Γ) ([Γ] ∙ [B]) =
--   let [A] , x = fundamentalVar x∷A∈Γ x◂p∈Γ [Γ]
--       [A]′ = wk1ᵛ [Γ] (maybeEmbᵛ [Γ] [B]) [A]
--   in  {![A]′!} , λ [σ] σ®σ′ → {!!}
--   -- let [Γ] = F.valid ⊢Γ
--   -- in  [Γ] , {!!}

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
fundamental (var x x₁) γ▸t = {!!} , {!!} , {!!}
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
fundamental (prodrecⱼ x x₁ Γ⊢t:A x₂ Γ⊢t:A₁) γ▸t = {!!}
fundamental (zeroⱼ ⊢Γ) γ▸t = zeroʳ ⊢Γ
fundamental (sucⱼ {n = t} Γ⊢t:ℕ) γ▸t =
  let invUsageSuc δ▸t γ≤δ = inv-usage-suc γ▸t
      [Γ] , [ℕ] , ⊩ʳt = fundamental Γ⊢t:ℕ δ▸t
      δ⊩ʳsuct = sucʳ [Γ] [ℕ] ⊩ʳt Γ⊢t:ℕ
      γ⊩ʳsuct = subsumption {t = suc t} {A = ℕ} [Γ] [ℕ] δ⊩ʳsuct γ≤δ
  in  [Γ] , [ℕ] , γ⊩ʳsuct
fundamental (natrecⱼ {G = A} {s = s} {z = z} {n = n} Γ⊢A Γ⊢z:A Γ⊢s:A Γ⊢n:ℕ) γ▸t =
  let invUsageNatrec δ▸z η▸s θ▸n le = inv-usage-natrec γ▸t
      [Γ]   , [A₀]  , ⊩ʳz  = fundamental Γ⊢z:A δ▸z
      [ΓℕA] , [A₊]′ , ⊩ʳs′ = fundamental Γ⊢s:A η▸s
      [Γ]′  , [ℕ]′  , ⊩ʳn′ = fundamental Γ⊢n:ℕ θ▸n
      [ℕ] = ℕᵛ {l = ¹} [Γ]
      [Γℕ] = [Γ] ∙ [ℕ]
      [Γℕ]′ , [A]′ = F.fundamental Γ⊢A
      [A] = IS.irrelevance {A = A} [Γℕ]′ [Γℕ] [A]′
      [A₊] = IS.irrelevance {A = wk1 (A [ (suc (var x0)) ]↑)} [ΓℕA] ([Γℕ] ∙ [A]) [A₊]′
      ⊩ʳs = irrelevance [ΓℕA] ([Γℕ] ∙ [A]) [A₊]′ [A₊] ⊩ʳs′
      ⊩ʳn = irrelevance [Γ]′ [Γ] [ℕ]′ [ℕ] ⊩ʳn′
  in  [Γ] , {!!} , {!!}
fundamental {Γ = Γ} {γ = γ} (Emptyrecⱼ {p = p} {A = A} {e = t} ⊢A Γ⊢t:Empty) γ▸t =
  let invUsageEmptyrec δ▸t γ≤δ = inv-usage-Emptyrec γ▸t
      [Γ] , [Empty] , ⊩ʳt = fundamental Γ⊢t:Empty δ▸t
      [Γ]′ , [A]′ = F.fundamental ⊢A
      [A] = IS.irrelevance {A = A} [Γ]′ [Γ] [A]′
      δ⊩ʳEmptyrec = Emptyrecʳ {t = t} {A = A} {p = p} [Γ] [Empty] ⊩ʳt [A]
      γ⊩ʳEmptyrec : γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ Emptyrec p A t ∷ A / [Γ] / [A]
      γ⊩ʳEmptyrec = subsumption {t = Emptyrec p A t} {A = A}
                                [Γ] [A] δ⊩ʳEmptyrec γ≤δ
  in  [Γ] , [A] , γ⊩ʳEmptyrec
fundamental (starⱼ ⊢Γ) γ▸t = starʳ ⊢Γ
fundamental (conv Γ⊢t:A x) γ▸t =
  let [Γ] , [A]′ , t®v = fundamental Γ⊢t:A γ▸t
  in  [Γ] , convᵛ {!!} {!!} {!!} {!!} [A]′ , {!!}
