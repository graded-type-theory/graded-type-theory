open import Definition.Modality.Instances.Erasure
open import Definition.Modality.Restrictions
open import Definition.Typed.EqualityRelation
open import Definition.Untyped Erasure as U hiding (_∷_)
open import Definition.Typed Erasure

module Erasure.LogicalRelation.Fundamental.Product
  {k} {Δ : Con Term k} (⊢Δ : ⊢ Δ)
  (restrictions : Restrictions Erasure)
  {{eqrel : EqRelSet Erasure}}
  where

open EqRelSet {{...}}

open import Definition.Untyped.Properties Erasure
open import Definition.Typed.Properties Erasure
open import Definition.Typed.RedSteps Erasure
open import Definition.Typed.Weakening Erasure
open import Definition.Typed.Consequences.Inversion Erasure
open import Definition.Typed.Consequences.Injectivity Erasure
open import Definition.Typed.Consequences.Substitution Erasure
open import Definition.Typed.Consequences.Syntactic Erasure
open import Definition.Typed.Consequences.RedSteps Erasure
open import Definition.Typed.Consequences.Reduction Erasure

open import Definition.LogicalRelation Erasure
open import Definition.LogicalRelation.Fundamental Erasure
open import Definition.LogicalRelation.Properties.Escape Erasure
open import Definition.LogicalRelation.Substitution Erasure
open import Definition.LogicalRelation.Substitution.Properties Erasure
open import Definition.LogicalRelation.Substitution.Introductions.Fst Erasure
open import Definition.LogicalRelation.Substitution.Introductions.Pi Erasure
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst Erasure
open import Definition.LogicalRelation.Substitution.Introductions.Universe Erasure

import Definition.LogicalRelation.Irrelevance Erasure as I
import Definition.LogicalRelation.Weakening Erasure as W
import Definition.LogicalRelation.Substitution.Irrelevance Erasure as IS

open import Definition.Modality.Instances.Erasure.Modality restrictions
open import Definition.Modality.Context ErasureModality
open import Definition.Modality.Instances.Erasure.Properties
  restrictions
open import Definition.Modality.Usage ErasureModality
open import Definition.Modality.Usage.Inversion ErasureModality
open import Definition.Mode ErasureModality

open import Erasure.LogicalRelation ⊢Δ restrictions
open import Erasure.LogicalRelation.Conversion ⊢Δ restrictions
open import Erasure.LogicalRelation.Reduction ⊢Δ restrictions
open import Erasure.LogicalRelation.Subsumption ⊢Δ restrictions
open import Erasure.LogicalRelation.Irrelevance ⊢Δ restrictions

open import Erasure.Extraction
import Erasure.Target as T
import Erasure.Target.Properties as TP

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
open import Tools.Sum using (inj₁; inj₂)
open import Tools.Unit
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PropositionalEquality

private
  variable
    n : Nat
    Γ : Con Term n
    A F t u : Term n
    t₁ t₂ : Term n
    v₁ v₂ : T.Term n
    G : Term (1+ n)
    p q r : Erasure
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
ΠΣʳ {F = F} {G = G} [Γ] ⊢ΠΣ =
    [U]
  , subsumptionMode (ΠΣ⟨ _ ⟩ _ , _ ▷ F ▹ G) [U] λ [σ] _ →
      Uᵣ (substitutionTerm ⊢ΠΣ (wellformedSubst [Γ] ⊢Δ [σ]) ⊢Δ)
  where
  [U] = Uᵛ [Γ]

prodʳ :
  ∀ {l} →
  ([Γ] : ⊩ᵛ Γ)
  ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
  ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
  ([G[t]] : Γ ⊩ᵛ⟨ l ⟩ G [ t ] / [Γ])
  ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ F / [Γ] / [F])
  ([u] : Γ ⊩ᵛ⟨ l ⟩ u ∷ G [ t ] / [Γ] / [G[t]])
  (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ᵐ· p ] F / [Γ] / [F])
  (⊩ʳu : δ ▸ Γ ⊩ʳ⟨ l ⟩ u ∷[ m ] G [ t ] / [Γ] / [G[t]]) →
  ∃ λ ([Σ] : Γ ⊩ᵛ⟨ l ⟩ Σ⟨ s ⟩ p , q ▷ F ▹ G / [Γ]) →
    p ·ᶜ γ +ᶜ δ ▸ Γ ⊩ʳ⟨ l ⟩ prod s p t u ∷[ m ] Σ p , q ▷ F ▹ G / [Γ] /
      [Σ]
prodʳ
  {Γ = Γ} {F = F} {G = G} {t = t} {u = u} {γ = γ} {m = m} {p = p}
  {δ = δ} {s = s} {q = q} {l = l} [Γ] [F] [G] [G[t]] [t] [u] ⊩ʳt ⊩ʳu =
  [Σ] , lemma m ⊩ʳt ⊩ʳu
  where
  [Σ] = Σᵛ [Γ] [F] [G]

  lemma :
    ∀ m →
    (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ᵐ· p ] F / [Γ] / [F])
    (⊩ʳu : δ ▸ Γ ⊩ʳ⟨ l ⟩ u ∷[ m ] G [ t ] / [Γ] / [G[t]]) →
    p ·ᶜ γ +ᶜ δ ▸ Γ ⊩ʳ⟨ l ⟩ prod s p t u ∷[ m ] Σ p , q ▷ F ▹ G / [Γ] /
      [Σ]
  lemma 𝟘ᵐ = _

  lemma 𝟙ᵐ ⊩ʳt ⊩ʳu {σ = σ} {σ′ = σ′} [σ] σ®σ′ =
      subst σ t , subst σ u , id ⊢prod , [σt]′
    , T.subst σ′ (erase u) , u®u″
    , lemma′ p ⊩ʳt σ®σ′ₜ
    where
        σ®σ′ₜ = subsumptionSubst {l = l} σ®σ′ (+ᶜ-decreasingˡ _ δ)
        σ®σ′ᵤ = subsumptionSubst {l = l} σ®σ′ (+ᶜ-decreasingʳ _ δ)
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
        u®u″ = irrelevanceTerm′ (PE.trans (singleSubstLift G t)
                                          (PE.cong (_[ _ ]) (PE.sym (wk-lift-id (subst (liftSubst σ) G)))))
                                [σG[t]] [σG[t]]″ u®u′

        lemma′ :
          ∀ p →
          γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ ⌞ p ⌟ ] F / [Γ] / [F] →
          σ ®⟨ l ⟩ σ′ ∷[ 𝟙ᵐ ] Γ ◂ p ·ᶜ γ / [Γ] / [σ] →
          Σ-® _ _ _ _
            (T.subst σ′ (erase (prod s p t u))) (T.subst σ′ (erase u)) p
        lemma′ 𝟘 _   _    = T.refl
        lemma′ ω ⊩ʳt σ®σ′ =
            T.subst σ′ (erase t)
          , T.refl
          , irrelevanceTerm′ (PE.sym (wk-id (subst σ F))) [σF] [σF]′
              (⊩ʳt [σ]
                 (PE.subst (λ γ → _ ®⟨ l ⟩ _ ∷[ _ ] _ ◂ γ / _ / _)
                    (≈ᶜ→≡ (·ᶜ-identityˡ _))
                    σ®σ′))

fstʳ′ : ∀ {l} {Γ : Con Term n}
      → ([Γ] : ⊩ᵛ Γ)
        ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
        ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
        ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Σₚ p , q ▷ F ▹ G / [Γ] / Σᵛ [Γ] [F] [G])
        (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ] Σₚ p , q ▷ F ▹ G
               / [Γ] / Σᵛ [Γ] [F] [G])
      → γ ▸[ m ] fst p t
      → γ ▸ Γ ⊩ʳ⟨ l ⟩ fst p t ∷[ m ] F / [Γ] / [F]
fstʳ′ {m = 𝟘ᵐ} = _

fstʳ′ {p = 𝟘} {m = 𝟙ᵐ} _ _ _ _ _ γ▸fst =
  case inv-usage-fst γ▸fst of λ where
    (invUsageFst 𝟘ᵐ () _ _ _)
    (invUsageFst 𝟙ᵐ 𝟙ᵐ≡ᵐ𝟘ᵐ? _ _ ok) → case ok PE.refl of λ where
      (inj₁ ())
      (inj₂ ok) →
        case
          𝟙ᵐ        ≡⟨ 𝟙ᵐ≡ᵐ𝟘ᵐ? ⟩
          𝟘ᵐ?       ≡⟨ 𝟘ᵐ?≡𝟘ᵐ ⟩
          𝟘ᵐ[ ok ]  ∎
        of λ ()
  where
  open Tools.Reasoning.PropositionalEquality

fstʳ′ {F = F} {G = G} {t = t} {p = ω} {q = q} {m = 𝟙ᵐ}
      [Γ] [F] [G] [t] ⊩ʳt γ▸fst {σ = σ} [σ] σ®σ′ =
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
                  (Σ-β₁ ⊢σF ⊢σG ⊢t₁′ ⊢t₂′ ⊢t′ PE.refl)
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
    ∀ m
    (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ] Σₚ p , q ▷ F ▹ G / [Γ] /
             Σᵛ [Γ] [F] [G]) →
    γ ▸ Γ ⊩ʳ⟨ l ⟩ snd p t ∷[ m ] G [ fst p t ] / [Γ] / [G[t₁]]
  lemma 𝟘ᵐ = _

  lemma 𝟙ᵐ ⊩ʳt {σ = σ} [σ] σ®σ′ =
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
                   (redMany (Σ-β₁ ⊢σF ⊢σG ⊢t₁′ ⊢t₂′ ⊢t′ PE.refl))
          t′≡t₁ = subset*Term
                    (fst-subst* t⇒t′ ⊢σF ⊢σG ⇨∷*
                     redMany (Σ-β₁ ⊢σF ⊢σG ⊢t₁′ ⊢t₂′ ⊢t′ PE.refl))
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
          t⇒u′ = t⇒u ⇨∷* redMany (Σ-β₂ ⊢σF ⊢σG ⊢t₁′ ⊢t₂′ ⊢t′ PE.refl)
          t⇒u″ = conv* t⇒u′ G[t]≡G[t₁]′
          v⇒w = case Σ-®-view extra of λ where
            (𝟘 v⇒v′)     → v⇒v′
            (ω _ v⇒v′ _) →
              TP.red*concat (TP.snd-subst* v⇒v′)
                (T.trans T.Σ-β₂ T.refl)
          wk[σ] = wkSubstS {σ = σ} [Γ] ⊢Δ ⊢Δ id [σ]
          wk[σF] = W.wk id ⊢Δ [σF]
          wk[t₁] = I.irrelevanceTerm′ (wk-subst F) wk[σF] (proj₁ (unwrap [F] ⊢Δ wk[σ])) [t₁]
          wk[Gt₁] = I.irrelevance′ (PE.sym (singleSubstWkComp t₁ σ G)) (proj₁ (unwrap [G] ⊢Δ (wk[σ] , wk[t₁])))
          t₂®v₂′ = redSubstTerm* wk[Gt₁] t₂®v₂ t⇒u″ v⇒w
      in  convTermʳ _ wk[Gt₁] (proj₁ (unwrap [G[t₁]] ⊢Δ [σ]))
            G[t′]≡G[t₁]′ t₂®v₂′

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
