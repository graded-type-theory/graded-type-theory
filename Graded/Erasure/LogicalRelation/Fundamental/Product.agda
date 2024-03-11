------------------------------------------------------------------------
-- Erasure validity of products and projections.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Erasure.LogicalRelation.Assumptions
open import Graded.Modality
open import Graded.Usage.Restrictions

module Graded.Erasure.LogicalRelation.Fundamental.Product
  {a} {M : Set a}
  {𝕄 : Modality M}
  (open Modality 𝕄)
  (UR : Usage-restrictions 𝕄)
  {TR : Type-restrictions 𝕄}
  (as : Assumptions TR)
  ⦃ 𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet ⦄
  where

open Assumptions as
open Type-restrictions TR

open import Definition.Untyped M hiding (_∷_)
open import Definition.Untyped.Properties M
open import Definition.Typed TR
open import Definition.Typed.Properties TR
open import Definition.Typed.RedSteps TR
open import Definition.Typed.Weakening TR hiding (wk)
open import Definition.Typed.Consequences.Inversion TR
open import Definition.Typed.Consequences.Injectivity TR
open import Definition.Typed.Consequences.Substitution TR
open import Definition.Typed.Consequences.Syntactic TR
open import Definition.Typed.Consequences.RedSteps TR
open import Definition.Typed.Consequences.Reduction TR

open import Definition.LogicalRelation TR
open import Definition.LogicalRelation.Fundamental TR
open import Definition.LogicalRelation.Properties.Escape TR
open import Definition.LogicalRelation.Substitution TR
open import Definition.LogicalRelation.Substitution.Escape TR
open import Definition.LogicalRelation.Substitution.Properties TR
open import Definition.LogicalRelation.Substitution.Introductions.Fst TR
open import Definition.LogicalRelation.Substitution.Introductions.Pi TR
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst TR
open import Definition.LogicalRelation.Substitution.Introductions.Universe TR

import Definition.LogicalRelation.Irrelevance TR as I
import Definition.LogicalRelation.Weakening TR as W
import Definition.LogicalRelation.Substitution.Irrelevance TR as IS

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Modality.Properties 𝕄
open import Graded.Usage 𝕄 UR
open import Graded.Usage.Inversion 𝕄 UR
open import Graded.Mode 𝕄

open import Graded.Erasure.LogicalRelation as
open import Graded.Erasure.LogicalRelation.Conversion as
open import Graded.Erasure.LogicalRelation.Reduction as
open import Graded.Erasure.LogicalRelation.Subsumption as
open import Graded.Erasure.LogicalRelation.Irrelevance as
open import Graded.Erasure.LogicalRelation.Value as

open import Graded.Erasure.Extraction 𝕄
open import Graded.Erasure.Extraction.Properties 𝕄
import Graded.Erasure.Target as T
import Graded.Erasure.Target.Properties as TP
open import Graded.Erasure.Target.Reasoning

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum using (inj₁; inj₂)

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
    s : Strength
    b : BinderMode
    m : Mode

ΠΣʳ :
  ∀ F G ([Γ] : ⊩ᵛ Γ) →
  ∃ λ ([U] : Γ ⊩ᵛ⟨ ¹ ⟩ U / [Γ]) →
  γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G ∷[ m ] U / [Γ] / [U]
ΠΣʳ {m = m} _ _ [Γ] =
    [U] , λ _ _ → Uᵣ (λ _ → T.refl) ◀ ⌜ m ⌝
  where
  [U] = Uᵛ [Γ]

prodʳ :
  ∀ {l} →
  {_⊕ᶜ_ : Conₘ n → Conₘ n → Conₘ n} →
  ([Γ] : ⊩ᵛ Γ)
  ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
  ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
  ([G[t]] : Γ ⊩ᵛ⟨ l ⟩ G [ t ]₀ / [Γ])
  ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ F / [Γ] / [F])
  ([u] : Γ ⊩ᵛ⟨ l ⟩ u ∷ G [ t ]₀ / [Γ] / [G[t]])
  (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ᵐ· p ] F / [Γ] / [F])
  (⊩ʳu : δ ▸ Γ ⊩ʳ⟨ l ⟩ u ∷[ m ] G [ t ]₀ / [Γ] / [G[t]]) →
  (∀ {x γ δ} → (γ ⊕ᶜ δ) ⟨ x ⟩ PE.≡ 𝟘 → γ ⟨ x ⟩ PE.≡ 𝟘) →
  (∀ {x γ δ} → (γ ⊕ᶜ δ) ⟨ x ⟩ PE.≡ 𝟘 → δ ⟨ x ⟩ PE.≡ 𝟘) →
  Σ-allowed s p q →
  ∃ λ ([Σ] : Γ ⊩ᵛ⟨ l ⟩ Σ⟨ s ⟩ p , q ▷ F ▹ G / [Γ]) →
    ((p ·ᶜ γ) ⊕ᶜ δ) ▸ Γ ⊩ʳ⟨ l ⟩ prod s p t u ∷[ m ] Σ p , q ▷ F ▹ G / [Γ] /
      [Σ]
prodʳ
  {Γ = Γ} {F = F} {G = G} {t = t} {u = u} {γ = γ} {m = 𝟘ᵐ} {p = p}
  {δ = δ} {s = s} {q = q} {l = l}
  [Γ] [F] [G] [G[t]] [t] [u] ⊩ʳt ⊩ʳu _ _ ok
    with is-𝟘? 𝟘
... | yes 𝟘≡𝟘 = Σᵛ [Γ] [F] [G] ok , _
... | no 𝟘≢𝟘 = ⊥-elim (𝟘≢𝟘 PE.refl)
prodʳ
  {Γ = Γ} {F = F} {G = G} {t = t} {u = u} {γ = γ} {m = 𝟙ᵐ} {p = p}
  {δ = δ} {s = s} {q = q} {l = l} {_⊕ᶜ_}
  [Γ] [F] [G] [G[t]] [t] [u] ⊩ʳt ⊩ʳu propˡ propʳ ok =
  [Σ] , lemma ⊩ʳt ⊩ʳu
  where
  [Σ] = Σᵛ [Γ] [F] [G] ok

  lemma :
    (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ ⌞ p ⌟ ] F / [Γ] / [F])
    (⊩ʳu : δ ▸ Γ ⊩ʳ⟨ l ⟩ u ∷[ 𝟙ᵐ ] G [ t ]₀ / [Γ] / [G[t]]) →
    (p ·ᶜ γ ⊕ᶜ δ) ▸ Γ ⊩ʳ⟨ l ⟩ prod s p t u ∷[ 𝟙ᵐ ] Σ p , q ▷ F ▹ G / [Γ] / [Σ]
  lemma ⊩ʳt ⊩ʳu {σ = σ} {σ′ = σ′} [σ] σ®σ′ = prod®prod ◀ 𝟙
    where
    σ®σ′ᵤ = subsumptionSubst σ®σ′ λ _ → propʳ
    u®u′ = ⊩ʳu [σ] σ®σ′ᵤ
    [σF] = proj₁ (unwrap [F] ⊢Δ [σ])
    [σF]′ = W.wk id ⊢Δ [σF]
    [σG[t]] = proj₁ (unwrap [G[t]] ⊢Δ [σ])
    [σt] = proj₁ ([t] ⊢Δ [σ])
    [σt]′ = I.irrelevanceTerm′ (PE.sym (wk-id (F [ σ ]))) [σF] [σF]′ [σt]
    [σt]″ = I.irrelevanceTerm′ (wk-subst F) [σF]′ (proj₁ (unwrap [F] ⊢Δ (wkSubstS [Γ] ⊢Δ ⊢Δ id [σ]))) [σt]′
    [σG[t]]′ = proj₁ (unwrap [G] ⊢Δ (wkSubstS [Γ] ⊢Δ ⊢Δ id [σ] , [σt]″))
    [σG[t]]″ = I.irrelevance′ (PE.sym (singleSubstWkComp (t [ σ ]) σ G)) [σG[t]]′
    ⊢σF = escape [σF]
    ⊢σG = escape (proj₁ (unwrap [G] (⊢Δ ∙ ⊢σF) (liftSubstS {σ = σ} {F = F} [Γ] ⊢Δ [F] [σ])))
    ⊢σt = escapeTerm [σF] [σt]
    ⊢σu = escapeTerm [σG[t]] (proj₁ ([u] ⊢Δ [σ]))
    ⊢prod = prodⱼ ⊢σF ⊢σG ⊢σt
              (PE.subst (λ x → Δ ⊢ u [ σ ] ∷ x)
                 (singleSubstLift G t) ⊢σu)
              ok
    σGt≡ρσGt = PE.trans (singleSubstLift G t)
                        (PE.cong (_[ _ ]₀) (PE.sym (wk-lift-id (G [ liftSubst σ ]))))
    u®u″ = irrelevanceQuant′ _ σGt≡ρσGt [σG[t]] [σG[t]]″ u®u′
             ◀≢𝟘 non-trivial
    open Tools.Reasoning.PropositionalEquality
    prod®prod = case is-𝟘? p of λ where
      (yes p≡𝟘) →
        let d = PE.subst (λ x → x T.[ σ′ ] T.⇒* _)
                         (PE.sym (prod-𝟘 s p≡𝟘))
                         T.refl
        in t [ σ ] , u [ σ ] , id ⊢prod , [σt]′ ,
           erase str u T.[ σ′ ] , u®u″ , Σ-®-intro-𝟘 d p≡𝟘
      (no p≢𝟘) →
        let σ®σ′ₜ = subsumptionSubst σ®σ′ λ x pγ⊕δ≡𝟘 →
              case PE.trans (PE.sym (lookup-distrib-·ᶜ γ p x))
                            (propˡ pγ⊕δ≡𝟘) of λ pγ≡𝟘 →
              case zero-product pγ≡𝟘 of λ where
                (inj₁ p≡𝟘) → ⊥-elim (p≢𝟘 p≡𝟘)
                (inj₂ γx≡𝟘) → γx≡𝟘
            t₁®v₁ = ⊩ʳt [σ] (subsumptionSubstMode σ®σ′ₜ)
            t₁®v₁′ = irrelevanceQuant′ _ (PE.sym (wk-id _))
                       [σF] [σF]′ t₁®v₁
            t₁®v₁″ = t₁®v₁′ ◀≢𝟘 λ ⌞p⌟≡𝟘 → non-trivial
              (begin
                𝟙         ≡˘⟨ PE.cong ⌜_⌝ (≢𝟘→⌞⌟≡𝟙ᵐ p≢𝟘) ⟩
                ⌜ ⌞ p ⌟ ⌝ ≡⟨ ⌞p⌟≡𝟘 ⟩
                𝟘 ∎)
        in case PE.singleton str of λ where
          (T.non-strict , PE.refl) →
            t [ σ ] , u [ σ ] , id ⊢prod , [σt]′ ,
            erase str u T.[ σ′ ] , u®u″ ,
            Σ-®-intro-ω _
              (PE.subst ((T._⇒* _) ∘→ T._[ σ′ ])
                 (PE.sym (prod-ω s p≢𝟘)) T.refl)
              t₁®v₁″ p≢𝟘
          (T.strict , PE.refl) →
            case reduces-to-value PE.refl [σF]′ t₁®v₁″ of λ
              (v₁ , v₁-val , erase-t[σ′]⇒*v₁) →
            case reduces-to-value PE.refl [σG[t]]″ u®u″ of λ
              (v₂ , v₂-val , erase-u[σ′]⇒*v₂) →
            _ , _ , id ⊢prod , [σt]′ , _ ,
            targetRedSubstTerm*′ [σG[t]]″ u®u″ erase-u[σ′]⇒*v₂ ,
            Σ-®-intro-ω _
              (PE.subst (λ v → v T.[ σ′ ] T.⇒* T.prod v₁ v₂)
                 (PE.sym (prod-ω s p≢𝟘))
                 (T.lam (T.lam (T.prod (T.var x1) (T.var x0)))
                    T.∘⟨ T.strict ⟩ (erase T.strict t T.[ σ′ ])
                    T.∘⟨ T.strict ⟩ (erase T.strict u T.[ σ′ ])  ⇒*⟨ TP.app-subst* $ TP.app-subst*-arg T.lam erase-t[σ′]⇒*v₁ ⟩

                  T.lam (T.lam (T.prod (T.var x1) (T.var x0)))
                    T.∘⟨ T.strict ⟩ v₁
                    T.∘⟨ T.strict ⟩ (erase T.strict u T.[ σ′ ])  ⇒⟨ T.app-subst $ T.β-red v₁-val ⟩

                  T.lam (T.prod (T.wk1 v₁) (T.var x0))
                    T.∘⟨ T.strict ⟩ (erase T.strict u T.[ σ′ ])  ⇒*⟨ TP.app-subst*-arg T.lam erase-u[σ′]⇒*v₂ ⟩

                  T.lam (T.prod (T.wk1 v₁) (T.var x0))
                    T.∘⟨ T.strict ⟩ v₂                           ⇒⟨ T.β-red v₂-val ⟩

                  T.prod (T.wk1 v₁ T.[ v₂ ]₀) v₂                 ≡⟨ PE.cong (flip T.prod v₂) $ TP.wk1-sgSubst _ _ ⟩⇒

                  T.prod v₁ v₂                                   ∎⇒))
              (targetRedSubstTerm*′ [σF]′ t₁®v₁″ erase-t[σ′]⇒*v₁)
              p≢𝟘


fstʳ′ : ∀ {l} {Γ : Con Term n}
      → ([Γ] : ⊩ᵛ Γ)
        ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
        ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
        (ok : Σˢ-allowed p q)
        ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Σˢ p , q ▷ F ▹ G / [Γ] / Σᵛ [Γ] [F] [G] ok)
        (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ] Σˢ p , q ▷ F ▹ G
               / [Γ] / Σᵛ [Γ] [F] [G] ok)
      → γ ▸[ m ] fst p t
      → γ ▸ Γ ⊩ʳ⟨ l ⟩ fst p t ∷[ m ] F / [Γ] / [F]
fstʳ′ {m = 𝟘ᵐ} with is-𝟘? 𝟘
... | yes 𝟘≡𝟘 = _
... | no 𝟘≢𝟘 = ⊥-elim (𝟘≢𝟘 PE.refl)
fstʳ′ {F = F} {G = G} {p = p} {q = q} {t = t} {m = 𝟙ᵐ}
      [Γ] [F] [G] ok [t] ⊩ʳt γ▸fst {σ = σ} [σ] σ®σ′ with is-𝟘? 𝟙
... | yes 𝟙≡𝟘 = _
... | no 𝟙≢𝟘 with is-𝟘? p
... | yes PE.refl =
  case inv-usage-fst γ▸fst of λ where
    (invUsageFst 𝟘ᵐ () _ _ _)
    (invUsageFst 𝟙ᵐ _ _ _ fst-ok) →
      ⊥-elim (𝟘≰𝟙 (fst-ok PE.refl))
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
      _ , _ , _ , _ , _ , ⊢t₁ , ⊢t₂ , Σ≡Σ′ , _ = inversion-prod ⊢t′
      F≡F′ , G≡G′ , _ = Σ-injectivity Σ≡Σ′
      ⊢t₁′ = conv ⊢t₁ (sym F≡F′)
      ⊢t₂′ = conv ⊢t₂ (substTypeEq (sym G≡G′) (refl ⊢t₁′))
      fstt⇒t₁ = fst-subst* t⇒t′ ⊢σF ⊢σG ⇨∷* redMany
                  (Σ-β₁ ⊢σF ⊢σG ⊢t₁′ ⊢t₂′ PE.refl ok)
      fstt⇒t₁′ = PE.subst (λ x → Δ ⊢ _ ⇒* _ ∷ x) (PE.sym (wk-id (F [ σ ]))) fstt⇒t₁
      fstv⇒v₁ = TP.red*concat (TP.fst-subst* v⇒v′) (T.trans T.Σ-β₁ T.refl)
      fstt®fstv = redSubstTerm* [σF]′ t₁®v₁ fstt⇒t₁′ fstv⇒v₁
  in  irrelevanceTerm′ (wk-id (F [ σ ])) [σF]′ [σF] fstt®fstv

fstʳ : Γ ⊢ F → Γ ∙ F ⊢ G → Γ ⊢ t ∷ Σˢ p , q ▷ F ▹ G
     → ([Γ] : ⊩ᵛ Γ) ([Σ] : Γ ⊩ᵛ⟨ ¹ ⟩ Σˢ p , q ▷ F ▹ G / [Γ])
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
      ok = ⊩ᵛΠΣ→ΠΣ-allowed [Σ]
      [Σ]′ = Σᵛ {F = F} {G = G} {q = q} [Γ] [F] [G] ok
      [Γ]₃ , [Σ]″ , [t]′ = fundamentalTerm Γ⊢t:Σ
      [t] = IS.irrelevanceTerm {A = Σ p , q ▷ F ▹ G} {t = t}
              [Γ]₃ [Γ] [Σ]″ [Σ]′ [t]′
      ⊩ʳt′ = irrelevance {A = Σ p , q ▷ F ▹ G} {t = t}
               [Γ] [Γ] [Σ] [Σ]′ ⊩ʳt
  in  [F] , fstʳ′ {F = F} {G = G} {t = t} [Γ] [F] [G] ok [t] ⊩ʳt′ γ▸fst


sndʳ′ :
  ∀ {l} {Γ : Con Term n}
  ([Γ] : ⊩ᵛ Γ)
  ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
  ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
  (ok : Σˢ-allowed p q)
  ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Σˢ p , q ▷ F ▹ G / [Γ] / Σᵛ [Γ] [F] [G] ok)
  (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ] Σˢ p , q ▷ F ▹ G / [Γ] /
           Σᵛ [Γ] [F] [G] ok) →
  ∃ λ ([G] : Γ ⊩ᵛ⟨ l ⟩ G [ fst p t ]₀ / [Γ]) →
    γ ▸ Γ ⊩ʳ⟨ l ⟩ snd p t ∷[ m ] G [ fst p t ]₀ / [Γ] / [G]
sndʳ′ {F = F} {G = G} {p = p} {q = q} {t = t} {m = m} {l = l} {Γ = Γ}
      [Γ] [F] [G] ok [t] ⊩ʳt =
  [G[t₁]] , lemma m ⊩ʳt
  where
  [Σ] = Σᵛ [Γ] [F] [G] ok
  [t₁] = fstᵛ {t = t} [Γ] [F] [G] ok [t]
  [G[t₁]] = substSΠ (BΣ 𝕤 p q) [Γ] [F] [Σ] [t₁]

  lemma :
    ∀ m →
    (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ] Σˢ p , q ▷ F ▹ G / [Γ] /
             Σᵛ [Γ] [F] [G] ok) →
    γ ▸ Γ ⊩ʳ⟨ l ⟩ snd p t ∷[ m ] G [ fst p t ]₀ / [Γ] / [G[t₁]]
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
          _ , _ , _ , _ , _ , ⊢t₁ , ⊢t₂ , eq , _ = inversion-prod ⊢t′
          eq₁ , eq₂ , _ = Σ-injectivity eq
          ⊢t₁′ = conv ⊢t₁ (sym eq₁)
          eq₂′ = substitutionEq eq₂ (substRefl (singleSubst ⊢t₁′)) ⊢Δ
          ⊢t₂′ = conv ⊢t₂ (sym eq₂′)
          t≡t₁ = subset*Term
                   (redMany (Σ-β₁ {p = p} ⊢σF ⊢σG ⊢t₁′ ⊢t₂′ PE.refl ok))
          t′≡t₁ = subset*Term
                    (fst-subst* t⇒t′ ⊢σF ⊢σG ⇨∷*
                     redMany (Σ-β₁ ⊢σF ⊢σG ⊢t₁′ ⊢t₂′ PE.refl ok))
          G[t]≡G[t₁] = substTypeEq (refl ⊢σG) t≡t₁
          G[t]≡G[t₁]′ = PE.subst (Δ ⊢ G [ liftSubst σ ] [ _ ]₀ ≡_)
                                 (PE.cong (_[ t₁ ]₀)
                                          (PE.sym (wk-lift-id (G [ liftSubst σ ]))))
                                 G[t]≡G[t₁]
          G[t′]≡G[t₁] = substTypeEq (refl ⊢σG) t′≡t₁
          G[t′]≡G[t₁]′ = PE.subst₂ (Δ ⊢_≡_)
            (PE.cong (_[ t₁ ]₀)
               (PE.sym (wk-lift-id (G [ liftSubst σ ]))))
            (PE.sym (singleSubstLift G (fst p t)))
            (sym G[t′]≡G[t₁])
          t⇒u = conv* (snd-subst* t⇒t′ ⊢σF ⊢σG)
                      (substTypeEq (refl ⊢σG) (fst-cong ⊢σF ⊢σG (subset*Term t⇒t′)))
          t⇒u′ = t⇒u ⇨∷* redMany (Σ-β₂ ⊢σF ⊢σG ⊢t₁′ ⊢t₂′ PE.refl ok)
          t⇒u″ = PE.subst (λ x → Δ ⊢ snd p t [ σ ] ⇒* t₂ ∷ x) (PE.sym (singleSubstLift G (fst p t)))
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
               sndt [ σ ] ®⟨ l ⟩ erase str sndt T.[ σ′ ] ∷
               G [ fst p t ]₀ [ σ ] / [σGt₁])
            extra
            (λ v⇒v′ p≡𝟘 → PE.subst (λ x → sndt [ σ ] ®⟨ l ⟩ x T.[ σ′ ] ∷ G [ fst p t ]₀ [ σ ] / [σGt₁])
                                   (PE.sym (snd-𝟘 p≡𝟘))
                                   (redSubstTerm* [σGt₁] t₂®v₂′ t⇒u″ v⇒v′))
            λ v₁ v⇒v′ t₁®v₁ p≢𝟘 →
              let v⇒v″ = TP.red*concat (TP.snd-subst* v⇒v′) (T.trans T.Σ-β₂ T.refl)
              in  PE.subst (λ x → snd p t [ σ ] ®⟨ l ⟩ x T.[ σ′ ] ∷ G [ fst p t ]₀ [ σ ] / [σGt₁])
                           (PE.sym (snd-ω p≢𝟘))
                           (redSubstTerm* [σGt₁] t₂®v₂′ t⇒u″ v⇒v″)

sndʳ : Γ ⊢ F → Γ ∙ F ⊢ G → Γ ⊢ t ∷ Σˢ p , q ▷ F ▹ G
     → ([Γ] : ⊩ᵛ Γ) ([Σ] : Γ ⊩ᵛ⟨ ¹ ⟩ Σˢ p , q ▷ F ▹ G / [Γ])
     → (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ t ∷[ m ] Σˢ p , q ▷ F ▹ G / [Γ] / [Σ])
     → ∃ λ ([G] : Γ ⊩ᵛ⟨ ¹ ⟩ G [ fst p t ]₀ / [Γ])
     → γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ snd p t ∷[ m ] G [ fst p t ]₀ / [Γ] / [G]
sndʳ {t = t} Γ⊢F Γ⊢G Γ⊢t:Σ [Γ] [Σ] ⊩ʳt =
  let [Γ]₁ , [F]′ = fundamental Γ⊢F
      [Γ]₂ , [G]′ = fundamental Γ⊢G
      [F] = IS.irrelevance [Γ]₁ [Γ] [F]′
      [G] = IS.irrelevance [Γ]₂ ([Γ] ∙ [F]) [G]′
      ok = ⊩ᵛΠΣ→ΠΣ-allowed [Σ]
      [Σ]′ = Σᵛ [Γ] [F] [G] ok
      ⊩ʳt′ = irrelevance {t = t} [Γ] [Γ] [Σ] [Σ]′ ⊩ʳt
      [Γ]₃ , [Σ]″ , [t]′ = fundamentalTerm Γ⊢t:Σ
      [t] = IS.irrelevanceTerm {t = t} [Γ]₃ [Γ] [Σ]″ [Σ]′ [t]′
  in  sndʳ′ {t = t} [Γ] [F] [G] ok [t] ⊩ʳt′
