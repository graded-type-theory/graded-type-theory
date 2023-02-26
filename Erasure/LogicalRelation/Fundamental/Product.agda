open import Definition.Modality.Instances.Erasure
open import Definition.Modality.Restrictions
open import Definition.Typed.EqualityRelation

module Erasure.LogicalRelation.Fundamental.Product
  (restrictions : Restrictions Erasure)
  {{eqrel : EqRelSet Erasure}}
  where

open EqRelSet {{...}}

open import Definition.Untyped Erasure as U hiding (_∷_)
open import Definition.Untyped.Properties Erasure
open import Definition.Typed Erasure
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

open import Erasure.LogicalRelation restrictions
open import Erasure.LogicalRelation.Conversion restrictions
open import Erasure.LogicalRelation.Reduction restrictions
open import Erasure.LogicalRelation.Subsumption restrictions
open import Erasure.LogicalRelation.Irrelevance restrictions

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
    t₁ t₂ : Term 0
    v₁ v₂ : T.Term 0
    G : Term (1+ n)
    p q r : Erasure
    γ δ : Conₘ n
    σ : Subst 0 n
    σ′ : T.Subst 0 n
    s : SigmaMode
    m : Mode

Σʳ : ([Γ] : ⊩ᵛ Γ) → Γ ⊢ Σ p , q ▷ F ▹ G ∷ U
   → ∃ λ ([U] : Γ ⊩ᵛ⟨ ¹ ⟩ U / [Γ])
   → γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ Σ⟨ s ⟩ p , q ▷ F ▹ G ∷[ m ] U / [Γ] / [U]
Σʳ {F = F} {G = G} [Γ] ⊢Σ =
    [U]
  , subsumptionMode (Σ⟨ _ ⟩ _ , _ ▷ F ▹ G) [U]
      (λ [σ] _ → Uᵣ (substitutionTerm ⊢Σ (wellformedSubst [Γ] ε [σ]) ε))
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
        [σF] = proj₁ (unwrap [F] ε [σ])
        [σF]′ = W.wk id ε [σF]
        [σG[t]] = proj₁ (unwrap [G[t]] ε [σ])
        [σt] = proj₁ ([t] ε [σ])
        [σt]′ = I.irrelevanceTerm′ (PE.sym (wk-id (subst σ F))) [σF] [σF]′ [σt]
        [σt]″ = I.irrelevanceTerm′ (wk-subst F) [σF]′ (proj₁ (unwrap [F] ε (wkSubstS [Γ] ε ε id [σ]))) [σt]′
        [σG[t]]′ = proj₁ (unwrap [G] ε (wkSubstS [Γ] ε ε id [σ] , [σt]″))
        [σG[t]]″ = I.irrelevance′ (PE.sym (singleSubstWkComp (subst σ t) σ G)) [σG[t]]′
        ⊢σF = escape [σF]
        ⊢σG = escape (proj₁ (unwrap [G] (ε ∙ ⊢σF) (liftSubstS {σ = σ} {F = F} [Γ] ε [F] [σ])))
        ⊢σt = escapeTerm [σF] [σt]
        ⊢σu = escapeTerm [σG[t]] (proj₁ ([u] ε [σ]))
        ⊢prod = prodⱼ ⊢σF ⊢σG ⊢σt (PE.subst (λ x → ε ⊢ subst σ u ∷ x) (singleSubstLift G t) ⊢σu)
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
  let [σF] = proj₁ (unwrap [F] ε [σ])
      [σF]′ = W.wk id ε [σF]
      ⊢σF = escape [σF]
      [⇑σ] = liftSubstS {σ = σ} {F = F} [Γ] ε [F] [σ]
      [σG] = proj₁ (unwrap [G] {σ = liftSubst σ} (ε ∙ ⊢σF) [⇑σ])
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
      fstt⇒t₁′ = PE.subst (λ x → ε ⊢ _ ⇒* _ ∷ x) (PE.sym (wk-id (subst σ F))) fstt⇒t₁
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
          [σF] = proj₁ (unwrap [F] ε [σ])
          ⊢σF = escape [σF]
          [⇑σ] = liftSubstS {σ = σ} {F = F} [Γ] ε [F] [σ]
          [σG] = proj₁ (unwrap [G] {σ = liftSubst σ} (ε ∙ ⊢σF) [⇑σ])
          ⊢σG = escape [σG]
          _ , _ , ⊢t′ = syntacticRedTerm t⇒t′
          _ , _ , _ , _ , _ , ⊢t₁ , ⊢t₂ , eq = inversion-prod ⊢t′
          eq₁ , eq₂ , _ = Σ-injectivity eq
          ⊢t₁′ = conv ⊢t₁ (sym eq₁)
          eq₂′ = substitutionEq eq₂ (substRefl (singleSubst ⊢t₁′)) ε
          ⊢t₂′ = conv ⊢t₂ (sym eq₂′)
          t≡t₁ = subset*Term
                   (redMany (Σ-β₁ ⊢σF ⊢σG ⊢t₁′ ⊢t₂′ ⊢t′ PE.refl))
          t′≡t₁ = subset*Term
                    (fst-subst* t⇒t′ ⊢σF ⊢σG ⇨∷*
                     redMany (Σ-β₁ ⊢σF ⊢σG ⊢t₁′ ⊢t₂′ ⊢t′ PE.refl))
          G[t]≡G[t₁] = substTypeEq (refl ⊢σG) t≡t₁
          G[t]≡G[t₁]′ = PE.subst (ε ⊢ subst (liftSubst σ) G [ _ ] ≡_)
                                 (PE.cong (_[ t₁ ])
                                          (PE.sym (wk-lift-id (subst (liftSubst σ) G))))
                                 G[t]≡G[t₁]
          G[t′]≡G[t₁] = substTypeEq (refl ⊢σG) t′≡t₁
          G[t′]≡G[t₁]′ = PE.subst₂ (ε ⊢_≡_)
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
          wk[σ] = wkSubstS {σ = σ} [Γ] ε ε id [σ]
          wk[σF] = W.wk id ε [σF]
          wk[t₁] = I.irrelevanceTerm′ (wk-subst F) wk[σF] (proj₁ (unwrap [F] ε wk[σ])) [t₁]
          wk[Gt₁] = I.irrelevance′ (PE.sym (singleSubstWkComp t₁ σ G)) (proj₁ (unwrap [G] ε (wk[σ] , wk[t₁])))
          t₂®v₂′ = redSubstTerm* wk[Gt₁] t₂®v₂ t⇒u″ v⇒w
      in  convTermʳ _ wk[Gt₁] (proj₁ (unwrap [G[t₁]] ε [σ]))
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

prodrecʳ′ :
  ∀ {l} {Γ : Con Term n}
  ([Γ] : ⊩ᵛ Γ)
  ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
  ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F]) →
  let [Σ] = Σᵛ [Γ] [F] [G] in
  ([A] : Γ ∙ (Σᵣ p , q ▷ F ▹ G) ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ [Σ])
  ([A₊] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ A [ prodᵣ p (var (x0 +1)) (var x0) ]↑² /
            [Γ] ∙ [F] ∙ [G])
  (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ ⌞ r ⌟ ] Σᵣ p , q ▷ F ▹ G / [Γ] / [Σ])
  (⊩ʳu : δ ∙ r · p ∙ r ▸ Γ ∙ F ∙ G ⊩ʳ⟨ l ⟩ u ∷[ 𝟙ᵐ ]
           A [ prodᵣ p (var (x0 +1)) (var x0) ]↑² /
           [Γ] ∙ [F] ∙ [G] / [A₊])
  ([At] : Γ ⊩ᵛ⟨ l ⟩ A [ t ] / [Γ])
  ([u] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ u ∷ A [ prodᵣ p (var (x0 +1)) (var x0) ]↑² /
           [Γ] ∙ [F] ∙ [G] / [A₊])
  ([σ] : ε ⊩ˢ σ ∷ Γ / [Γ] / ε)
  (σ®σ′ : σ ®⟨ l ⟩ σ′ ∷[ 𝟙ᵐ ] Γ ◂ r ·ᶜ γ +ᶜ δ / [Γ] / [σ])
  ([σt] : ε ⊩⟨ l ⟩ subst σ t ∷ subst σ (Σᵣ p , q ▷ F ▹ G) /
            proj₁ (unwrap [Σ] ε [σ])) →
  subst σ (prodrec r p A t u) ®⟨ l ⟩
    T.subst σ′ (erase (prodrec r p A t u)) ∷ subst σ (A [ t ]) /
    proj₁ (unwrap [At] ε [σ])
prodrecʳ′ _ _ _ _ _ _ _ _ _ _ _ (Σₜ _ _ _ (ne x) _) =
  PE.⊥-elim (noClosedNe x)

prodrecʳ′
  {n = n} {F = F} {G = G} {p = p′} {q = q} {A = A} {γ = γ} {t = t}
  {r = 𝟘} {δ = δ} {u = u} {σ = σ} {σ′ = σ′} {l = l} {Γ = Γ}
  [Γ] [F] [G] [A] [A₊] ⊩ʳt ⊩ʳu [At] [u] [σ] σ®σ′
  (Σₜ p d p≡p (prodₙ {t = p₁} {u = p₂})
     (PE.refl , wk[p₁] , wk[p₂] , PE.refl)) =
  let σ®σ′ᵤ = subsumptionSubst {l = l} σ®σ′ (+ᶜ-decreasingʳ (𝟘 ·ᶜ γ) δ)
      [σF] = proj₁ (unwrap [F] ε [σ])
      ⊢σF = escape [σF]
      ⊢ε = wf ⊢σF
      wk[σF] = W.wk id ⊢ε [σF]
      [p₁] = I.irrelevanceTerm′ (wk-id (subst σ F)) wk[σF] [σF] wk[p₁]
      [σGp₁] = proj₁ (unwrap [G] {σ = consSubst σ _} ε ([σ] , [p₁]))
      wk[σ] = wkSubstS [Γ] ε ⊢ε id [σ]
      wk[σGp₁] = I.irrelevance′ (PE.sym (singleSubstWkComp p₁ σ G))
                                (proj₁ (unwrap [G] ⊢ε (wk[σ] , I.irrelevanceTerm′ (wk-subst F)
                                                                           wk[σF]
                                                                           (proj₁ (unwrap [F] ⊢ε wk[σ]))
                                                                           wk[p₁])))
      [p₂] = I.irrelevanceTerm′ (PE.trans (PE.cong (_[ p₁ ]) (wk-lift-id (subst (liftSubst σ) G)))
                                          (singleSubstComp p₁ σ G))
                                wk[σGp₁] [σGp₁] wk[p₂]
      [σ₊] = ([σ] , [p₁]) , [p₂]
      u®u′ = ⊩ʳu {σ = consSubst (consSubst σ p₁) p₂}
                 {σ′ = T.consSubst (T.consSubst σ′ T.undefined) T.undefined}
                 [σ₊] ((σ®σ′ᵤ , tt) , tt)
      [⇑σ] = liftSubstS {σ = σ} {F = F} [Γ] ε [F] [σ]
      [σG] = proj₁ (unwrap [G] {σ = liftSubst σ} (ε ∙ ⊢σF) [⇑σ])
      ⊢σG = escape [σG]
      [Σ] = Σᵛ {F = F} {G} {q = q} {m = Σᵣ} [Γ] [F] [G]
      [σΣ] = proj₁ (unwrap [Σ] ε [σ])
      ⊢σΣ = escape [σΣ]
      [σA] = unwrap [A] {σ = liftSubst σ} (ε ∙ ⊢σΣ)
               (liftSubstS [Γ] ε [Σ] [σ]) .proj₁
      ⊢σA = escape [σA]
      [⇑²σ] = liftSubstS {σ = liftSubst σ} {F = G} (_∙_ {A = F} [Γ] [F]) (ε ∙ ⊢σF) [G] [⇑σ]
      [σA₊] = proj₁ (unwrap [A₊] {σ = liftSubstn σ 2} (ε ∙ ⊢σF ∙ ⊢σG) [⇑²σ])
      [σu] = proj₁ ([u] {σ = liftSubstn σ 2} (ε ∙ ⊢σF ∙ ⊢σG) [⇑²σ])
      ⊢σu = escapeTerm [σA₊] [σu]
      ⊢σu′ = PE.subst (λ x → _ ⊢ subst (liftSubstn σ 2) u ∷ x) (subst-β-prodrec A σ) ⊢σu
      red₁ = prodrec-subst* {r = 𝟘} (redₜ d) ⊢σF ⊢σG ⊢σA ⊢σu′
      ⊢p₁ = escapeTerm [σF] [p₁]
      ⊢p₂ = escapeTerm [σGp₁] [p₂]
      ⊢p₂′ = PE.subst (λ x → ε ⊢ p₂ ∷ x) (PE.sym (singleSubstComp p₁ σ G)) ⊢p₂
      At≡Ap = substTypeEq (refl ⊢σA) (subset*Term (redₜ d))
      red₂ = prodrec-β ⊢σF ⊢σG ⊢σA ⊢p₁ ⊢p₂′ ⊢σu′ PE.refl
      red = conv* red₁ At≡Ap ⇨∷* redMany red₂
      red′ = PE.subst₂ (λ x y → ε ⊢ _ ⇒* x ∷ y) (doubleSubstComp u p₁ p₂ σ)
                       (substCompProdrec A p₁ p₂ σ) red
      [σ₊A₊] = proj₁ (unwrap [A₊] {σ = consSubst (consSubst σ p₁) p₂} ε [σ₊])
      pr®u′ = sourceRedSubstTerm* [σ₊A₊] u®u′ red′
      [σAt] = proj₁ (unwrap [At] ε [σ])
  in  convTermʳ _ [σ₊A₊] [σAt]
        (PE.subst₂ (λ x y → ε ⊢ x ≡ y) (substCompProdrec A p₁ p₂ σ)
           (PE.sym (singleSubstLift A t)) (sym At≡Ap))
        (PE.subst
           (λ x → subst σ (prodrec 𝟘 p′ A t u) ®⟨ l ⟩ x ∷
                    subst (consSubst (consSubst σ p₁) p₂)
                      (A [ prodᵣ p′ (var (x0 +1)) (var x0) ]↑²) /
                    [σ₊A₊])
           (PE.sym
              (PE.trans
                 (TP.doubleSubstLift σ′ (erase u) T.undefined
                    T.undefined)
                 (TP.doubleSubstComp (erase u) T.undefined
                    T.undefined σ′)))
           pr®u′)

prodrecʳ′
  {n = n} {F = F} {G = G} {p = p′} {q = q} {A = A} {γ = γ} {t = t}
  {r = ω} {δ = δ} {u = u} {σ = σ} {σ′ = σ′} {l = l} {Γ = Γ}
  [Γ] [F] [G] [A] [A₊] ⊩ʳt ⊩ʳu [At] [u] [σ] σ®σ′
  (Σₜ p d p≡p prodₙ (PE.refl , wk[p₁]′ , wk[p₂] , PE.refl))
  with ⊩ʳt [σ]
         (subsumptionSubst {l = l} σ®σ′
            (≤ᶜ-trans (+ᶜ-decreasingˡ (ω ·ᶜ γ) δ)
               (≤ᶜ-reflexive (·ᶜ-identityˡ γ))))
... | p₁ , p₂ , t⇒p , wk[p₁] , q₂ , p₂®q₂ , extra
  with prod-PE-injectivity (whrDet*Term (redₜ d , prodₙ) (t⇒p , prodₙ))
     | wf (escape (proj₁ (unwrap [F] ε [σ])))
... | _ , _ , PE.refl , PE.refl | ε =
  let _ , red″ , u®u′ = lemma p′ [A₊] ⊩ʳu extra
      pr®pr′          = redSubstTerm* [σ₊A₊] u®u′ red′ red″
  in
  convTermʳ _ [σ₊A₊] [σAt]
    (PE.subst₂ (λ x y → ε ⊢ x ≡ y)
               (substCompProdrec A p₁ p₂ σ)
               (PE.sym (singleSubstLift A t)) (sym At≡Ap))
    pr®pr′
  where
      [σF]   = proj₁ (unwrap [F] ε [σ])
      wk[σF] = W.wk id ε [σF]
      σ®σ′ᵤ = subsumptionSubst {l = l} σ®σ′ (+ᶜ-decreasingʳ (ω ·ᶜ γ) δ)
      ⊢σF = escape [σF]
      [p₁] = I.irrelevanceTerm′ (wk-id (subst σ F)) wk[σF] [σF] wk[p₁]
      [σGp₁] = proj₁ (unwrap [G] {σ = consSubst σ p₁} ε ([σ] , [p₁]))
      wk[σ] = wkSubstS [Γ] ε ε id [σ]
      wk[σGp₁] = λ x → I.irrelevance′ (PE.sym (singleSubstWkComp p₁ σ G))
                                (proj₁ (unwrap [G] ε (wk[σ] , I.irrelevanceTerm′ (wk-subst F)
                                                                           wk[σF]
                                                                           (proj₁ (unwrap [F] ε wk[σ]))
                                                                           x)))
      [p₂] = I.irrelevanceTerm′ (PE.trans (PE.cong (_[ p₁ ]) (wk-lift-id (subst (liftSubst σ) G)))
                                          (singleSubstComp p₁ σ G))
                                (wk[σGp₁] wk[p₁]′) [σGp₁] wk[p₂]
      p₂®q₂′ = irrelevanceTerm′ (PE.trans (PE.cong (_[ p₁ ]) (wk-lift-id (subst (liftSubst σ) G)))
                                          (singleSubstComp p₁ σ G))
                                (wk[σGp₁] wk[p₁]) [σGp₁] p₂®q₂
      [σ₊] = ([σ] , [p₁]) , [p₂]
      [⇑σ] = liftSubstS {σ = σ} {F = F} [Γ] ε [F] [σ]
      [σG] = proj₁ (unwrap [G] {σ = liftSubst σ} (ε ∙ ⊢σF) [⇑σ])
      ⊢σG = escape [σG]
      [Σ] = Σᵛ {F = F} {G} {q = q} {m = Σᵣ} [Γ] [F] [G]
      [σΣ] = proj₁ (unwrap [Σ] ε [σ])
      ⊢σΣ = escape [σΣ]
      [σA] = unwrap [A] {σ = liftSubst σ} (ε ∙ ⊢σΣ)
               (liftSubstS [Γ] ε [Σ] [σ]) .proj₁
      ⊢σA = escape [σA]
      [⇑²σ] = liftSubstS {σ = liftSubst σ} {F = G} (_∙_ {A = F} [Γ] [F]) (ε ∙ ⊢σF) [G] [⇑σ]
      [σA₊] = proj₁ (unwrap [A₊] {σ = liftSubstn σ 2} (ε ∙ ⊢σF ∙ ⊢σG) [⇑²σ])
      [σu] = proj₁ ([u] {σ = liftSubstn σ 2} (ε ∙ ⊢σF ∙ ⊢σG) [⇑²σ])
      ⊢σu = escapeTerm [σA₊] [σu]
      ⊢σu′ = PE.subst (λ x → _ ⊢ subst (liftSubstn σ 2) u ∷ x) (subst-β-prodrec A σ) ⊢σu
      red₁ = prodrec-subst* {r = ω} (redₜ d) ⊢σF ⊢σG ⊢σA ⊢σu′
      ⊢p₁ = escapeTerm [σF] [p₁]
      ⊢p₂ = escapeTerm [σGp₁] [p₂]
      ⊢p₂′ = PE.subst (λ x → ε ⊢ p₂ ∷ x) (PE.sym (singleSubstComp p₁ σ G)) ⊢p₂
      At≡Ap = substTypeEq (refl ⊢σA) (subset*Term (redₜ d))
      red₂ = prodrec-β ⊢σF ⊢σG ⊢σA ⊢p₁ ⊢p₂′ ⊢σu′ PE.refl
      red′ = PE.subst₂
        (λ x y → ε ⊢ _ ⇒* x ∷ y)
        (doubleSubstComp u p₁ p₂ σ)
        (substCompProdrec A p₁ p₂ σ)
        (conv* red₁ At≡Ap ⇨∷* redMany red₂)
      [σ₊A₊] = proj₁ (unwrap [A₊] {σ = consSubst (consSubst σ p₁) p₂} ε [σ₊])
      [σAt] = proj₁ (unwrap [At] ε [σ])

      lemma :
        ∀ p′ →
        ([A₊] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩
                  A [ prodᵣ p′ (var (x0 +1)) (var x0) ]↑² /
                  [Γ] ∙ [F] ∙ [G]) →
        (⊩ʳu : δ ∙ p′ ∙ ω ▸ Γ ∙ F ∙ G ⊩ʳ⟨ l ⟩ u ∷[ 𝟙ᵐ ]
                 A [ prodᵣ p′ (var (x0 +1)) (var x0) ]↑² /
                 [Γ] ∙ [F] ∙ [G] / [A₊]) →
        Σ-® l _ _ p₁ _ q₂ p′ →
        ∃ λ u′ →
        T.subst σ′ (erase (prodrec ω p′ A t u)) T.⇒* u′ ×
        subst (consSubst (consSubst σ p₁) p₂) u ®⟨ l ⟩ u′ ∷
          subst (consSubst (consSubst σ p₁) p₂)
            (subst
               (consSubst (λ x → var ((x +1) +1))
                  (prodᵣ p′ (var (x0 +1)) (var x0)))
               A) /
          unwrap [A₊] ε [σ₊] .proj₁
      lemma 𝟘 [A₊] ⊩ʳu v⇒q =
          _
        , T.trans T.β-red T.refl
        , PE.subst
            (λ u′ →
               subst (consSubst (consSubst σ p₁) p₂) u ®⟨ l ⟩ u′ ∷
               subst (consSubst (consSubst σ p₁) p₂)
                 (subst
                    (consSubst (λ x → var ((x +1) +1))
                       (prodᵣ 𝟘 (var (x0 +1)) (var x0)))
                    A) /
               unwrap [A₊] ε [σ₊] .proj₁)
            (let open Tools.Reasoning.PropositionalEquality in
             T.subst (T.consSubst (T.consSubst σ′ T.undefined)
                        (T.subst σ′ (erase t)))
               (erase u)                                                  ≡⟨ TP.substVar-to-subst
                                                                               (λ where
                                                                                  x0 → PE.refl
                                                                                  (x0 +1) → PE.refl
                                                                                  ((_ +1) +1) → PE.refl)
                                                                               (erase u) ⟩

             T.subst (T.consSubst σ′ (T.subst σ′ (erase t)) T.ₛ•ₛ
                      T.liftSubst (T.sgSubst T.undefined))
               (erase u)                                                  ≡˘⟨ TP.substCompEq (erase u) ⟩

             T.subst (T.consSubst σ′ (T.subst σ′ (erase t)))
               (T.subst (T.liftSubst (T.sgSubst T.undefined)) (erase u))  ≡˘⟨ TP.singleSubstComp _ _
                                                                                (T.subst (T.liftSubst (T.sgSubst T.undefined)) (erase u)) ⟩
             T.subst (T.liftSubst σ′)
               (T.subst (T.liftSubst (T.sgSubst T.undefined)) (erase u))
               T.[ T.subst σ′ (erase t) ]                                 ∎)
            (⊩ʳu [σ₊]
               ((σ®σ′ᵤ , _) , redSubstTerm* [σGp₁] p₂®q₂′ (id ⊢p₂) v⇒q))
      lemma ω [A₊] ⊩ʳu (q₁ , v⇒q , p₁®q₁) =
          _
        , TP.red*concat red″₁ (T.trans red″₂ T.refl)
        , ⊩ʳu [σ₊] ((σ®σ′ᵤ , p₁®q₁′) , p₂®q₂′)
        where
        red″₁ = TP.prodrec-subst* v⇒q
        red″₂ = PE.subst
          (T.prodrec (T.prod q₁ q₂)
             (T.subst (T.liftSubstn σ′ 2) (erase u))
             T.⇒_)
          (TP.doubleSubstComp (erase u) q₁ q₂ σ′)
          T.prodrec-β
        p₁®q₁′ = irrelevanceTerm′ (wk-id (subst σ F)) wk[σF] [σF] p₁®q₁

prodrecʳ :
  ∀ {l} {Γ : Con Term n}
  ([Γ] : ⊩ᵛ Γ)
  ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
  ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
  ([Σ] : Γ ⊩ᵛ⟨ l ⟩ Σᵣ p , q ▷ F ▹ G / [Γ])
  ([A] : Γ ∙ (Σᵣ p , q ▷ F ▹ G) ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ [Σ])
  ([A₊] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ A [ prodᵣ p (var (x0 +1)) (var x0) ]↑² /
            [Γ] ∙ [F] ∙ [G])
  ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Σᵣ p , q ▷ F ▹ G / [Γ] / [Σ])
  ([u] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ u ∷ A [ prodᵣ p (var (x0 +1)) (var x0) ]↑² /
           [Γ] ∙ [F] ∙ [G] / [A₊])
  (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ᵐ· r ] Σᵣ p , q ▷ F ▹ G / [Γ] / [Σ])
  (⊩ʳu : δ ∙ ⌜ m ⌝ · (r · p) ∙ ⌜ m ⌝ · r ▸ Γ ∙ F ∙ G ⊩ʳ⟨ l ⟩ u ∷[ m ]
           A [ prodᵣ p (var (x0 +1)) (var x0) ]↑² / [Γ] ∙ [F] ∙ [G] /
           [A₊]) →
  ∃ λ ([At] : Γ ⊩ᵛ⟨ l ⟩ A [ t ] / [Γ]) →
    r ·ᶜ γ +ᶜ δ ▸ Γ ⊩ʳ⟨ l ⟩ prodrec r p A t u ∷[ m ] A [ t ] / [Γ] /
      [At]
prodrecʳ
  {F = F} {G = G} {p = p} {q = q} {A = A} {t = t} {u = u}
  {γ = γ} {m = m} {r = r} {δ = δ} {l = l} {Γ = Γ}
  [Γ] [F] [G] [Σ] [A] [A₊] [t] [u] ⊩ʳt ⊩ʳu =
  [At] , lemma m ⊩ʳt ⊩ʳu
  where
  [At] = substS {t = t} [Γ] [Σ] [A] [t]

  lemma :
    ∀ m →
    (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ᵐ· r ] Σᵣ p , q ▷ F ▹ G / [Γ] / [Σ])
    (⊩ʳu : δ ∙ ⌜ m ⌝ · (r · p) ∙ ⌜ m ⌝ · r ▸ Γ ∙ F ∙ G ⊩ʳ⟨ l ⟩ u ∷[ m ]
             A [ prodᵣ p (var (x0 +1)) (var x0) ]↑² / [Γ] ∙ [F] ∙ [G] /
             [A₊]) →
    r ·ᶜ γ +ᶜ δ ▸ Γ ⊩ʳ⟨ l ⟩ prodrec r p A t u ∷[ m ] A [ t ] / [Γ] /
      [At]
  lemma 𝟘ᵐ = _

  lemma 𝟙ᵐ ⊩ʳt ⊩ʳu {σ = σ} [σ] σ®σ′ =
    let [Σ]′ = Σᵛ [Γ] [F] [G]
        [A]′ = IS.irrelevance ([Γ] ∙ [Σ]) ([Γ] ∙ [Σ]′) [A]
        ⊩ʳt′ = irrelevance {t = t} [Γ] [Γ] [Σ] [Σ]′ ⊩ʳt
        [t]′ = IS.irrelevanceTerm {t = t} [Γ] [Γ] [Σ] [Σ]′ [t]
        [σt] = proj₁ ([t]′ ε [σ])
    in  prodrecʳ′ [Γ] [F] [G] [A]′ [A₊] ⊩ʳt′ ⊩ʳu [At] [u] [σ] σ®σ′ [σt]
