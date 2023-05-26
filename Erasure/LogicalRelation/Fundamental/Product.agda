------------------------------------------------------------------------
-- Erasure validity of products and projections.
------------------------------------------------------------------------

open import Definition.Modality
open import Definition.Typed.EqualityRelation
import Definition.Typed as T′
import Definition.Untyped as U hiding (_∷_)
open import Tools.Nullary
import Tools.PropositionalEquality as PE
open import Tools.Sum using (_⊎_; inj₁; inj₂)

module Erasure.LogicalRelation.Fundamental.Product
  {a k} {M : Set a} (𝕄 : Modality M)
  (open U M) (open T′ M) (open Modality 𝕄)
  {Δ : Con Term k} (⊢Δ : ⊢ Δ)
  (𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet)
  {{eqrel : EqRelSet M}}
  where
open EqRelSet {{...}}

open import Definition.Untyped.Properties M
open import Definition.Typed.Properties M
open import Definition.Typed.RedSteps M
open import Definition.Typed.Weakening M hiding (wk)
open import Definition.Typed.Consequences.Inversion M
open import Definition.Typed.Consequences.Injectivity M
open import Definition.Typed.Consequences.Substitution M
open import Definition.Typed.Consequences.Syntactic M
open import Definition.Typed.Consequences.RedSteps M
open import Definition.Typed.Consequences.Reduction M

open import Definition.LogicalRelation M
open import Definition.LogicalRelation.Fundamental M
open import Definition.LogicalRelation.Properties.Escape M
open import Definition.LogicalRelation.Substitution M
open import Definition.LogicalRelation.Substitution.Properties M
open import Definition.LogicalRelation.Substitution.Introductions.Fst M
open import Definition.LogicalRelation.Substitution.Introductions.Pi M
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst M
open import Definition.LogicalRelation.Substitution.Introductions.Universe M

import Definition.LogicalRelation.Irrelevance M as I
import Definition.LogicalRelation.Weakening M as W
import Definition.LogicalRelation.Substitution.Irrelevance M as IS

open import Definition.Modality.Context 𝕄
open import Definition.Modality.Context.Properties 𝕄
open import Definition.Modality.Properties.Has-well-behaved-zero
  semiring-with-meet-and-star 𝟘-well-behaved
open import Definition.Modality.Usage 𝕄
open import Definition.Modality.Usage.Inversion 𝕄
open import Definition.Mode 𝕄

open import Erasure.LogicalRelation 𝕄 ⊢Δ is-𝟘?
open import Erasure.LogicalRelation.Conversion 𝕄 ⊢Δ is-𝟘?
open import Erasure.LogicalRelation.Reduction 𝕄 ⊢Δ is-𝟘?
open import Erasure.LogicalRelation.Subsumption 𝕄 ⊢Δ is-𝟘?
open import Erasure.LogicalRelation.Irrelevance 𝕄 ⊢Δ is-𝟘?

open import Erasure.Extraction 𝕄 is-𝟘?
open import Erasure.Extraction.Properties 𝕄 𝟘-well-behaved
import Erasure.Target as T
import Erasure.Target.Properties as TP

open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.Reasoning.PropositionalEquality

private
  variable
    n : Nat
    Γ : Con Term n
    A F t u : Term n
    t₁ t₂ : Term n
    v₁ v₂ : T.Term n
    G : Term (1+ n)
    p q r : M
    γ δ : Conₘ n
    σ : Subst k n
    σ′ : T.Subst k n
    s : SigmaMode
    b : BinderMode
    m : Mode

ΠΣʳ :
  ([Γ] : ⊩ᵛ Γ) → Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G ∷ U →
  ∃ λ ([U] : Γ ⊩ᵛ⟨ ¹ ⟩ U / [Γ]) →
  γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G ∷[ m ] U / [Γ] / [U]
ΠΣʳ {F = F} {G = G} {m = m} [Γ] ⊢ΠΣ =
    [U] , λ [σ] σ®σ′ → Uᵣ (substitutionTerm ⊢ΠΣ (wellformedSubst [Γ] ⊢Δ [σ]) ⊢Δ) ◀ ⌜ m ⌝
  where
  [U] = Uᵛ [Γ]

prodʳ :
  ∀ {l} →
  {_⊕ᶜ_ : Conₘ n → Conₘ n → Conₘ n} →
  ([Γ] : ⊩ᵛ Γ)
  ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
  ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
  ([G[t]] : Γ ⊩ᵛ⟨ l ⟩ G [ t ] / [Γ])
  ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ F / [Γ] / [F])
  ([u] : Γ ⊩ᵛ⟨ l ⟩ u ∷ G [ t ] / [Γ] / [G[t]])
  (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ᵐ· p ] F / [Γ] / [F])
  (⊩ʳu : δ ▸ Γ ⊩ʳ⟨ l ⟩ u ∷[ m ] G [ t ] / [Γ] / [G[t]]) →
  (∀ {x γ δ} → (γ ⊕ᶜ δ) ⟨ x ⟩ PE.≡ 𝟘 → γ ⟨ x ⟩ PE.≡ 𝟘) →
  (∀ {x γ δ} → (γ ⊕ᶜ δ) ⟨ x ⟩ PE.≡ 𝟘 → δ ⟨ x ⟩ PE.≡ 𝟘) →
  ∃ λ ([Σ] : Γ ⊩ᵛ⟨ l ⟩ Σ⟨ s ⟩ p , q ▷ F ▹ G / [Γ]) →
    ((p ·ᶜ γ) ⊕ᶜ δ) ▸ Γ ⊩ʳ⟨ l ⟩ prod s p t u ∷[ m ] Σ p , q ▷ F ▹ G / [Γ] /
      [Σ]
prodʳ
  {Γ = Γ} {F = F} {G = G} {t = t} {u = u} {γ = γ} {m = 𝟘ᵐ} {p = p}
  {δ = δ} {s = s} {q = q} {l = l} [Γ] [F] [G] [G[t]] [t] [u] ⊩ʳt ⊩ʳu _ _
    with is-𝟘? 𝟘
... | yes 𝟘≡𝟘 = Σᵛ [Γ] [F] [G] , _
... | no 𝟘≢𝟘 = PE.⊥-elim (𝟘≢𝟘 PE.refl)
prodʳ
  {Γ = Γ} {F = F} {G = G} {t = t} {u = u} {γ = γ} {m = 𝟙ᵐ} {p = p}
  {δ = δ} {s = s} {q = q} {l = l} {_⊕ᶜ_} [Γ] [F] [G] [G[t]] [t] [u] ⊩ʳt ⊩ʳu
    propˡ propʳ =
    [Σ] , lemma ⊩ʳt ⊩ʳu
  where
  [Σ] = Σᵛ [Γ] [F] [G]

  lemma :
    (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ ⌞ p ⌟ ] F / [Γ] / [F])
    (⊩ʳu : δ ▸ Γ ⊩ʳ⟨ l ⟩ u ∷[ 𝟙ᵐ ] G [ t ] / [Γ] / [G[t]]) →
    (p ·ᶜ γ ⊕ᶜ δ) ▸ Γ ⊩ʳ⟨ l ⟩ prod s p t u ∷[ 𝟙ᵐ ] Σ p , q ▷ F ▹ G / [Γ] / [Σ]
  lemma ⊩ʳt ⊩ʳu {σ = σ} {σ′ = σ′} [σ] σ®σ′ =
    (subst σ t , subst σ u , id ⊢prod , [σt]′ , T.subst σ′ (erase u) , u®u″ , extra) ◀ 𝟙
    where
    σ®σ′ᵤ = subsumptionSubst {l = l} σ®σ′ λ _ → propʳ
    u®u′ = ⊩ʳu [σ] σ®σ′ᵤ
    [σF] = proj₁ (unwrap [F] ⊢Δ [σ])
    [σF]′ = W.wk id ⊢Δ [σF]
    [σG[t]] = proj₁ (unwrap [G[t]] ⊢Δ [σ])
    [σt] = proj₁ ([t] ⊢Δ [σ])
    [σt]′ = I.irrelevanceTerm′ (PE.sym (wk-id (subst σ F))) [σF] [σF]′ [σt]
    [σt]″ = I.irrelevanceTerm′ (wk-subst F) [σF]′ (proj₁ (unwrap [F] ⊢Δ (wkSubstS [Γ] ⊢Δ ⊢Δ id [σ]))) [σt]′
    [σG[t]]′ = proj₁ (unwrap [G] ⊢Δ (wkSubstS [Γ] ⊢Δ ⊢Δ id [σ] , [σt]″))
    [σG[t]]″ = I.irrelevance′ (PE.sym (singleSubstWkComp (subst σ t) σ G)) [σG[t]]′
    ⊢σF = escape [σF]
    ⊢σG = escape (proj₁ (unwrap [G] (⊢Δ ∙ ⊢σF) (liftSubstS {σ = σ} {F = F} [Γ] ⊢Δ [F] [σ])))
    ⊢σt = escapeTerm [σF] [σt]
    ⊢σu = escapeTerm [σG[t]] (proj₁ ([u] ⊢Δ [σ]))
    ⊢prod = prodⱼ ⊢σF ⊢σG ⊢σt (PE.subst (λ x → Δ ⊢ subst σ u ∷ x) (singleSubstLift G t) ⊢σu)
    σGt≡ρσGt = PE.trans (singleSubstLift G t)
                        (PE.cong (_[ _ ]) (PE.sym (wk-lift-id (subst (liftSubst σ) G))))
    u®u″ = irrelevanceQuant′ _ σGt≡ρσGt [σG[t]] [σG[t]]″ u®u′ ◀≢𝟘 𝟙≉𝟘
    open Tools.Reasoning.PropositionalEquality
    extra = case is-𝟘? p of λ where
              (yes p≡𝟘) →
                let d = PE.subst (λ x → T.subst σ′ x T.⇒* _)
                                 (PE.sym (prod-𝟘 {k = s} p≡𝟘))
                                 T.refl
                in  Σ-®-intro-𝟘 d p≡𝟘
              (no p≢𝟘) →
                let d = PE.subst (λ x → T.subst σ′ x T.⇒* _)
                                 (PE.sym (prod-ω {k = s} p≢𝟘))
                                 T.refl
                    σ®σ′ₜ = subsumptionSubst {l = l} σ®σ′ λ x pγ⊕δ≡𝟘 →
                      case PE.trans (PE.sym (lookup-distrib-·ᶜ γ p x))
                                    (propˡ pγ⊕δ≡𝟘) of λ pγ≡𝟘 →
                      case zero-product pγ≡𝟘 of λ where
                        (inj₁ p≡𝟘) → PE.⊥-elim (p≢𝟘 p≡𝟘)
                        (inj₂ γx≡𝟘) → γx≡𝟘
                    t₁®v₁ = ⊩ʳt [σ] (subsumptionSubstMode l σ®σ′ₜ)
                    t₁®v₁′ = irrelevanceQuant′ _ (PE.sym (wk-id _)) [σF] [σF]′ t₁®v₁
                    t₁®v₁″ = t₁®v₁′ ◀≢𝟘 λ ⌞p⌟≡𝟘 → 𝟙≉𝟘
                      (begin
                        𝟙         ≡˘⟨ PE.cong ⌜_⌝ (≉𝟘→⌞⌟≡𝟙ᵐ p≢𝟘) ⟩
                        ⌜ ⌞ p ⌟ ⌝ ≡⟨ ⌞p⌟≡𝟘 ⟩
                        𝟘 ∎)
                in  Σ-®-intro-ω (T.subst σ′ (erase t))
                                d t₁®v₁″ p≢𝟘


fstʳ′ : ∀ {l} {Γ : Con Term n}
      → ([Γ] : ⊩ᵛ Γ)
        ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
        ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
        ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Σₚ p , q ▷ F ▹ G / [Γ] / Σᵛ [Γ] [F] [G])
        (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ] Σₚ p , q ▷ F ▹ G
               / [Γ] / Σᵛ [Γ] [F] [G])
      → γ ▸[ m ] fst p t
      → γ ▸ Γ ⊩ʳ⟨ l ⟩ fst p t ∷[ m ] F / [Γ] / [F]
fstʳ′ {m = 𝟘ᵐ} with is-𝟘? 𝟘
... | yes 𝟘≡𝟘 = _
... | no 𝟘≢𝟘 = PE.⊥-elim (𝟘≢𝟘 PE.refl)
fstʳ′ {F = F} {G = G} {t = t} {p = p} {q = q} {m = 𝟙ᵐ}
      [Γ] [F] [G] [t] ⊩ʳt γ▸fst {σ = σ} [σ] σ®σ′ with is-𝟘? 𝟙
... | yes 𝟙≡𝟘 = _
... | no 𝟙≢𝟘 with is-𝟘? p
... | yes PE.refl =
  case inv-usage-fst γ▸fst of λ where
    (invUsageFst 𝟘ᵐ () _ _ _)
    (invUsageFst 𝟙ᵐ _ _ _ fst-ok) →
      PE.⊥-elim (𝟘≰𝟙 (fst-ok PE.refl))
... | no p≢𝟘 =
  let [σF] = proj₁ (unwrap [F] ⊢Δ [σ])
      [σF]′ = W.wk id ⊢Δ [σF]
      ⊢σF = escape [σF]
      [⇑σ] = liftSubstS {σ = σ} {F = F} [Γ] ⊢Δ [F] [σ]
      [σG] = proj₁ (unwrap [G] {σ = liftSubst σ} (⊢Δ ∙ ⊢σF) [⇑σ])
      ⊢σG = escape [σG]
      t₁ , t₂ , t⇒t′ , [t₁] , v₂ , t₂®v₂ , v₁ , v⇒v′ , t₁®v₁ =
        ⊩ʳt [σ] σ®σ′
      _ , _ , ⊢t′ = syntacticRedTerm t⇒t′
      _ , _ , _ , _ , _ , ⊢t₁ , ⊢t₂ , Σ≡Σ′ = inversion-prod ⊢t′
      F≡F′ , G≡G′ , _ = Σ-injectivity Σ≡Σ′
      ⊢t₁′ = conv ⊢t₁ (sym F≡F′)
      ⊢t₂′ = conv ⊢t₂ (substTypeEq (sym G≡G′) (refl ⊢t₁′))
      fstt⇒t₁ = fst-subst* t⇒t′ ⊢σF ⊢σG ⇨∷* redMany
                  (Σ-β₁ ⊢σF ⊢σG ⊢t₁′ ⊢t₂′ PE.refl)
      fstt⇒t₁′ = PE.subst (λ x → Δ ⊢ _ ⇒* _ ∷ x) (PE.sym (wk-id (subst σ F))) fstt⇒t₁
      fstv⇒v₁ = TP.red*concat (TP.fst-subst* v⇒v′) (T.trans T.Σ-β₁ T.refl)
      fstt®fstv = redSubstTerm* [σF]′ t₁®v₁ fstt⇒t₁′ fstv⇒v₁
  in  irrelevanceTerm′ (wk-id (subst σ F)) [σF]′ [σF] fstt®fstv

fstʳ : Γ ⊢ F → Γ ∙ F ⊢ G → Γ ⊢ t ∷ Σ p , q ▷ F ▹ G
     → ([Γ] : ⊩ᵛ Γ) ([Σ] : Γ ⊩ᵛ⟨ ¹ ⟩ Σ p , q ▷ F ▹ G / [Γ])
     → (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ t ∷[ m ] Σ p , q ▷ F ▹ G / [Γ] / [Σ])
     → γ ▸[ m ] fst p t
     → ∃ λ ([F] : Γ ⊩ᵛ⟨ ¹ ⟩ F / [Γ])
     → γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ fst p t ∷[ m ] F / [Γ] / [F]
fstʳ
  {Γ = Γ} {F = F} {G = G} {t = t} {p = p} {q = q}
  Γ⊢F Γ⊢G Γ⊢t:Σ [Γ] [Σ] ⊩ʳt γ▸fst =
  let [Γ]₁ , [F]′ = fundamental Γ⊢F
      [Γ]₂ , [G]′ = fundamental Γ⊢G
      [F] = IS.irrelevance {A = F} [Γ]₁ [Γ] [F]′
      [G] = IS.irrelevance {A = G} [Γ]₂ ([Γ] ∙ [F]) [G]′
      [Σ]′ = Σᵛ {F = F} {G = G} {q = q} [Γ] [F] [G]
      [Γ]₃ , [Σ]″ , [t]′ = fundamentalTerm Γ⊢t:Σ
      [t] = IS.irrelevanceTerm {A = Σ p , q ▷ F ▹ G} {t = t}
              [Γ]₃ [Γ] [Σ]″ [Σ]′ [t]′
      ⊩ʳt′ = irrelevance {A = Σ p , q ▷ F ▹ G} {t = t}
               [Γ] [Γ] [Σ] [Σ]′ ⊩ʳt
  in  [F] , fstʳ′ {F = F} {G = G} {t = t} [Γ] [F] [G] [t] ⊩ʳt′ γ▸fst


sndʳ′ :
  ∀ {l} {Γ : Con Term n}
  ([Γ] : ⊩ᵛ Γ)
  ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
  ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
  ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Σₚ p , q ▷ F ▹ G / [Γ] / Σᵛ [Γ] [F] [G])
  (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ] Σₚ p , q ▷ F ▹ G / [Γ] /
           Σᵛ [Γ] [F] [G]) →
  ∃ λ ([G] : Γ ⊩ᵛ⟨ l ⟩ G [ fst p t ] / [Γ]) →
    γ ▸ Γ ⊩ʳ⟨ l ⟩ snd p t ∷[ m ] G [ fst p t ] / [Γ] / [G]
sndʳ′ {F = F} {G = G} {t = t} {p = p} {q = q} {m = m} {l = l} {Γ = Γ}
      [Γ] [F] [G] [t] ⊩ʳt =
  [G[t₁]] , lemma m ⊩ʳt
  where
  [Σ] = Σᵛ [Γ] [F] [G]
  [t₁] = fstᵛ {t = t} [Γ] [F] [G] [t]
  [G[t₁]] = substSΠ (BΣ Σₚ p q) [Γ] [F] [Σ] [t₁]

  lemma :
    ∀ m →
    (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ] Σₚ p , q ▷ F ▹ G / [Γ] /
             Σᵛ [Γ] [F] [G]) →
    γ ▸ Γ ⊩ʳ⟨ l ⟩ snd p t ∷[ m ] G [ fst p t ] / [Γ] / [G[t₁]]
  lemma m ⊩ʳt {σ = σ} {σ′ = σ′} [σ] σ®σ′ with is-𝟘? ⌜ m ⌝
  ... | yes m≡𝟘 = _
  ... | no m≢𝟘 =
      let t₁ , t₂ , t⇒t′ , [t₁] , v₂ , t₂®v₂ , extra = ⊩ʳt [σ] σ®σ′
          [σF] = proj₁ (unwrap [F] ⊢Δ [σ])
          ⊢σF = escape [σF]
          [⇑σ] = liftSubstS {σ = σ} {F = F} [Γ] ⊢Δ [F] [σ]
          [σG] = proj₁ (unwrap [G] {σ = liftSubst σ} (⊢Δ ∙ ⊢σF) [⇑σ])
          ⊢σG = escape [σG]
          _ , _ , ⊢t′ = syntacticRedTerm t⇒t′
          _ , _ , _ , _ , _ , ⊢t₁ , ⊢t₂ , eq = inversion-prod ⊢t′
          eq₁ , eq₂ , _ = Σ-injectivity eq
          ⊢t₁′ = conv ⊢t₁ (sym eq₁)
          eq₂′ = substitutionEq eq₂ (substRefl (singleSubst ⊢t₁′)) ⊢Δ
          ⊢t₂′ = conv ⊢t₂ (sym eq₂′)
          t≡t₁ = subset*Term
                   (redMany (Σ-β₁ {p = p} ⊢σF ⊢σG ⊢t₁′ ⊢t₂′ PE.refl))
          t′≡t₁ = subset*Term
                    (fst-subst* t⇒t′ ⊢σF ⊢σG ⇨∷*
                     redMany (Σ-β₁ ⊢σF ⊢σG ⊢t₁′ ⊢t₂′ PE.refl))
          G[t]≡G[t₁] = substTypeEq (refl ⊢σG) t≡t₁
          G[t]≡G[t₁]′ = PE.subst (Δ ⊢ subst (liftSubst σ) G [ _ ] ≡_)
                                 (PE.cong (_[ t₁ ])
                                          (PE.sym (wk-lift-id (subst (liftSubst σ) G))))
                                 G[t]≡G[t₁]
          G[t′]≡G[t₁] = substTypeEq (refl ⊢σG) t′≡t₁
          G[t′]≡G[t₁]′ = PE.subst₂ (Δ ⊢_≡_)
            (PE.cong (_[ t₁ ])
               (PE.sym (wk-lift-id (subst (liftSubst σ) G))))
            (PE.sym (singleSubstLift G (fst p t)))
            (sym G[t′]≡G[t₁])
          t⇒u = conv* (snd-subst* t⇒t′ ⊢σF ⊢σG)
                      (substTypeEq (refl ⊢σG) (fst-cong ⊢σF ⊢σG (subset*Term t⇒t′)))
          t⇒u′ = t⇒u ⇨∷* redMany (Σ-β₂ ⊢σF ⊢σG ⊢t₁′ ⊢t₂′ PE.refl)
          t⇒u″ = PE.subst (λ x → Δ ⊢ subst σ (snd p t) ⇒* t₂ ∷ x) (PE.sym (singleSubstLift G (fst p t)))
                          (conv* t⇒u′ (trans G[t]≡G[t₁] (sym G[t′]≡G[t₁])))
          wk[σ] = wkSubstS {σ = σ} [Γ] ⊢Δ ⊢Δ id [σ]
          wk[σF] = W.wk id ⊢Δ [σF]
          wk[t₁] = I.irrelevanceTerm′ (wk-subst F) wk[σF] (proj₁ (unwrap [F] ⊢Δ wk[σ])) [t₁]
          wk[Gt₁] = I.irrelevance′ (PE.sym (singleSubstWkComp t₁ σ G)) (proj₁ (unwrap [G] ⊢Δ (wk[σ] , wk[t₁])))
          [σGt₁] = proj₁ (unwrap [G[t₁]] ⊢Δ [σ])
          t₂®v₂′ = convTermʳ wk[Gt₁] [σGt₁] G[t′]≡G[t₁]′ t₂®v₂
          sndt = snd p t
      in  Σ-®-elim
            (λ _ →
               subst σ sndt ®⟨ l ⟩ T.subst σ′ (erase sndt) ∷
               subst σ (G [ fst p t ]) / [σGt₁])
            extra
            (λ v⇒v′ p≡𝟘 → PE.subst (λ x → subst σ sndt ®⟨ l ⟩ T.subst σ′ x ∷ subst σ (G [ fst p t ]) / [σGt₁])
                                   (PE.sym (snd-𝟘 p≡𝟘))
                                   (redSubstTerm* [σGt₁] t₂®v₂′ t⇒u″ v⇒v′))
            λ v₁ v⇒v′ t₁®v₁ p≢𝟘 →
              let v⇒v″ = TP.red*concat (TP.snd-subst* v⇒v′) (T.trans T.Σ-β₂ T.refl)
              in  PE.subst (λ x → subst σ (snd p t) ®⟨ l ⟩ T.subst σ′ x ∷ subst σ (G [ fst p t ]) / [σGt₁])
                           (PE.sym (snd-ω p≢𝟘))
                           (redSubstTerm* [σGt₁] t₂®v₂′ t⇒u″ v⇒v″)

sndʳ : Γ ⊢ F → Γ ∙ F ⊢ G → Γ ⊢ t ∷ Σₚ p , q ▷ F ▹ G
     → ([Γ] : ⊩ᵛ Γ) ([Σ] : Γ ⊩ᵛ⟨ ¹ ⟩ Σₚ p , q ▷ F ▹ G / [Γ])
     → (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ t ∷[ m ] Σₚ p , q ▷ F ▹ G / [Γ] / [Σ])
     → ∃ λ ([G] : Γ ⊩ᵛ⟨ ¹ ⟩ G [ fst p t ] / [Γ])
     → γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ snd p t ∷[ m ] G [ fst p t ] / [Γ] / [G]
sndʳ {t = t} Γ⊢F Γ⊢G Γ⊢t:Σ [Γ] [Σ] ⊩ʳt =
  let [Γ]₁ , [F]′ = fundamental Γ⊢F
      [Γ]₂ , [G]′ = fundamental Γ⊢G
      [F] = IS.irrelevance [Γ]₁ [Γ] [F]′
      [G] = IS.irrelevance [Γ]₂ ([Γ] ∙ [F]) [G]′
      [Σ]′ = Σᵛ [Γ] [F] [G]
      ⊩ʳt′ = irrelevance {t = t} [Γ] [Γ] [Σ] [Σ]′ ⊩ʳt
      [Γ]₃ , [Σ]″ , [t]′ = fundamentalTerm Γ⊢t:Σ
      [t] = IS.irrelevanceTerm {t = t} [Γ]₃ [Γ] [Σ]″ [Σ]′ [t]′
  in  sndʳ′ {t = t} [Γ] [F] [G] [t] ⊩ʳt′
