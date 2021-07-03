{-# OPTIONS --without-K  #-}
open import Definition.Modality.Erasure

open import Definition.Typed.EqualityRelation


module Erasure.LogicalRelation.Fundamental.Prodrec {{eqrel : EqRelSet Erasure}} where
open EqRelSet {{...}}

open import Definition.Untyped Erasure as U hiding (_∷_) renaming (_[_,_] to _[_,,_])
open import Definition.Untyped.Properties Erasure
open import Definition.Typed Erasure
open import Definition.Typed.Properties Erasure
open import Definition.Typed.RedSteps Erasure
open import Definition.Typed.Reduction Erasure
open import Definition.Typed.Weakening Erasure
open import Definition.Typed.Consequences.Injectivity Erasure
open import Definition.Typed.Consequences.Inversion Erasure
open import Definition.Typed.Consequences.RedSteps Erasure
open import Definition.Typed.Consequences.Reduction Erasure
open import Definition.Typed.Consequences.Substitution Erasure
open import Definition.Typed.Consequences.Syntactic Erasure

open import Definition.LogicalRelation Erasure
import Definition.LogicalRelation.Weakening Erasure as W
import Definition.LogicalRelation.Irrelevance Erasure as I
open import Definition.LogicalRelation.Fundamental Erasure
open import Definition.LogicalRelation.Fundamental.Reducibility Erasure
open import Definition.LogicalRelation.Properties.Escape Erasure
open import Definition.LogicalRelation.ShapeView Erasure
open import Definition.LogicalRelation.Substitution Erasure
open import Definition.LogicalRelation.Substitution.Properties Erasure
open import Definition.LogicalRelation.Substitution.Introductions.Pi Erasure
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst Erasure
import Definition.LogicalRelation.Substitution.Irrelevance Erasure as IS

open import Definition.Modality.Context ErasureModality
open import Definition.Modality.Usage ErasureModality
open import Definition.Modality.Erasure.Properties

open import Erasure.LogicalRelation
open import Erasure.LogicalRelation.Conversion
open import Erasure.LogicalRelation.Properties
open import Erasure.LogicalRelation.Irrelevance

open import Erasure.Extraction
import Erasure.Target as T
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
    A F t u : Term n
    t₁ t₂ t′ : Term 0
    v₁ v₂ : T.Term 0
    G : Term (1+ n)
    p q : Erasure
    γ δ : Conₘ n
    σ : Subst 0 n
    σ′ : T.Subst 0 n


prodrec-𝟘 : ∀ {l} {Γ : Con Term n}
          → ([Γ] : ⊩ᵛ Γ)
            ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
            ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
            ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Σ q ▷ F ▹ G / [Γ] / Σᵛ {F = F} {G = G} {q = q} [Γ] [F] [G])
            ([σ] : ε ⊩ˢ σ ∷ Γ / [Γ] / ε)
          → ∃₂ λ t₁ t₂ → ε ⊢ subst σ t :⇒*: prod t₁ t₂ ∷ (subst σ (Σ q ▷ F ▹ G))
prodrec-𝟘 [Γ] [F] [G] [t] [σ] with proj₁ ([t] ε [σ])
... | Σₜ p t⇒p (prodₙ {t = t₁} {u = t₂}) _ _ _ = t₁ , t₂ , t⇒p
... | Σₜ p t⇒p (ne x) _ _ _ = PE.⊥-elim (noClosedNe x)

prodrecʳ : ∀ {l} {Γ : Con Term n}
         → ([Γ] : ⊩ᵛ Γ)
           ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
           ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
           (let [Σ] = Σᵛ {F = F} {G = G} {q = q} [Γ] [F] [G])
           ([A] : Γ ∙ (Σ q ▷ F ▹ G) ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ [Σ])
           ([A₊] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ A [ prod (var (x0 +1)) (var x0) ]↑² / [Γ] ∙ [F] ∙ [G])
           ([A[t]] : Γ ⊩ᵛ⟨ l ⟩ A [ t ] / [Γ])
           ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Σ q ▷ F ▹ G / [Γ] / [Σ])
           ([u] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ u ∷ A [ prod (var (x0 +1)) (var x0) ]↑² / [Γ] ∙ [F] ∙ [G] / [A₊])
         → γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷ Σ q ▷ F ▹ G / [Γ] / [Σ]
         → δ ∙ p ∙ p ▸ Γ ∙ F ∙ G ⊩ʳ⟨ l ⟩ u
             ∷ A [ prod (var (x0 +1)) (var x0) ]↑² / [Γ] ∙ [F] ∙ [G] / [A₊]
         → p ·ᶜ γ +ᶜ δ ▸ Γ ⊩ʳ⟨ l ⟩ prodrec p A t u ∷ A [ t ] / [Γ] / [A[t]]
prodrecʳ {n} {F} {G} {q} {A} {t} {u} {γ} {δ} {𝟘} {l} {Γ}
         [Γ] [F] [G] [A] [A₊] [A[t]] [t] [u] ⊩ʳt ⊩ʳu {σ} {σ′} [σ] σ®σ′ =
  let [Σ] = Σᵛ {F = F} {G = G} {q = q} [Γ] [F] [G]
      [σΣ] = proj₁ ([Σ] ε [σ])
      ⊢Σ = escape [σΣ]
      _  , Bᵣ F′ G′ D ⊢F ⊢G A≡A [F′] [G′] G-ext = extractMaybeEmb (Σ-elim [σΣ])
      [σF] = proj₁ ([F] ε [σ])
      [σA] = proj₁ ([A] {σ = liftSubst σ} (ε ∙ ⊢Σ) (liftSubstS {F = Σ q ▷ F ▹ G} [Γ] ε [Σ] [σ]))
      ⊢A = escape [σA]
      [σA₊] = proj₁ ([A₊] {σ = liftSubstn σ 2} (ε ∙ ⊢F ∙ ⊢G)
                          (liftSubstS {F = G} (_∙_ {A = F} [Γ] [F]) (ε ∙ ⊢F) [G]
                                      (liftSubstS {F = F} [Γ] ε [F] [σ])))
      [σu] = proj₁ ([u] {σ = liftSubstn σ 2} (ε ∙ ⊢F ∙ ⊢G) (liftSubstS {F = G} (_∙_ {A = F} [Γ] [F]) (ε ∙ ⊢F) [G]
                                                           (liftSubstS {F = F} [Γ] ε [F] [σ])))
      ⊢u = escapeTerm [σA₊] [σu]
      ⊢u′ = PE.subst (λ A → _ ⊢ subst (liftSubstn σ 2) u ∷ A) (subst-β-prodrec A σ) ⊢u
      p₁ , p₂ , t⇒p′ = prodrec-𝟘 {F = F} {G = G} {t = t} [Γ] [F] [G] [t] [σ]
      [ ⊢t , ⊢p , t⇒p ] = t⇒p′
      F″ , G″ , q″ , ⊢F″ , ⊢G″ , ⊢p₁′ , ⊢p₂′ , X≡Σ = inversion-prod ⊢p
      F≡F″ , G≡G″ , q≡q″ = Σ-injectivity X≡Σ
      ⊢p₁ = conv ⊢p₁′ (sym F≡F″)
      ⊢p₂″ = conv ⊢p₂′ (substTypeEq (sym G≡G″) (refl ⊢p₁))
      ⊢p₂ = PE.subst (ε ⊢ p₂ ∷_) (singleSubstComp p₁ σ G) ⊢p₂″
      [F]₁ , [p₁]′ = reducibleTerm ⊢p₁
      [p₁] = I.irrelevanceTerm [F]₁ [σF] [p₁]′
      [G]₁ , [p₂]′ = reducibleTerm ⊢p₂
      [σG[p₁]] = proj₁ ([G] ε ([σ] , [p₁]))
      [p₂] = I.irrelevanceTerm [G]₁ [σG[p₁]] [p₂]′
      [σA[p]] = proj₁ ([A₊] ε (([σ] , [p₁]) , [p₂]))
      σ®σ′ᵤ = subsumption′ {l = l} σ®σ′ (+ᶜ-decreasingʳ _ δ)
      u®w = ⊩ʳu {σ = consSubst (consSubst σ p₁) p₂}
                {σ′ = T.consSubst (T.consSubst σ′ T.undefined) T.undefined}
                (([σ] , [p₁]) , [p₂])
                ((σ®σ′ᵤ , tt) , tt)
      prt⇒prp = prodrec-subst* {p = 𝟘} t⇒p ⊢F ⊢G ⊢A ⊢t ⊢u′
      prt⇒prp′ = PE.subst (ε ⊢ prodrec 𝟘 _ _ _ ⇒* prodrec 𝟘 _ _ _ ∷_)
                          (substCompProdrec A p₁ p₂ σ)
                          (conv* prt⇒prp (substTypeEq (refl ⊢A) (subset*Term t⇒p)))
      prp⇒u = redMany (prodrec-β {p = 𝟘} ⊢F ⊢G ⊢p₁ ⊢p₂″ ⊢A ⊢u′)
      prp⇒u′ = PE.subst₂ (ε ⊢ prodrec 𝟘 _ _ _ ⇒*_∷_)
                         (doubleSubstComp u p₁ p₂ σ)
                         (substCompProdrec A p₁ p₂ σ)
                         prp⇒u
      prt⇒u = prt⇒prp′ ⇨∷* prp⇒u′
      pr®w = ®-red*ˡ [σA[p]] u®w prt⇒u
      pr®w′ = PE.subst (subst σ (prodrec 𝟘 A t u) ®⟨ l ⟩_∷
                              subst (consSubst (consSubst σ p₁) p₂)
                                    (A [ prod (var (x0 +1)) (var x0) ]↑²) / [σA[p]])
                       (PE.sym (PE.trans (TP.doubleSubstLift σ′ (erase u) T.undefined T.undefined)
                                         (TP.doubleSubstComp (erase u) T.undefined T.undefined σ′)))
                       pr®w
  in  convTermʳ [σA[p]] (proj₁ ([A[t]] ε [σ]))
                (PE.subst₂ (ε ⊢_≡_) (substCompProdrec A p₁ p₂ σ)
                                    (PE.sym (singleSubstLift A t))
                                    (sym (substTypeEq (refl ⊢A) (subset*Term t⇒p))))
                pr®w′

prodrecʳ {n} {F} {G} {q} {A} {t} {u} {γ} {δ} {ω} {l} {Γ}
         [Γ] [F] [G] [A] [A₊] [A[t]] [t] [u] ⊩ʳt ⊩ʳu {σ} {σ′} [σ] σ®σ′ =
  let [Σ] = Σᵛ {F = F} {G = G} {q = q} [Γ] [F] [G]
      [σΣ] = proj₁ ([Σ] ε [σ])
      ⊢Σ = escape [σΣ]
      _  , Bᵣ F′ G′ D ⊢F ⊢G A≡A [F′] [G′] G-ext = extractMaybeEmb (Σ-elim [σΣ])
      [σF] = proj₁ ([F] ε [σ])
      [σA] = proj₁ ([A] {σ = liftSubst σ} (ε ∙ ⊢Σ) (liftSubstS {F = Σ q ▷ F ▹ G} [Γ] ε [Σ] [σ]))
      ⊢A = escape [σA]
      [σt] = proj₁ ([t] ε [σ])
      ⊢t = escapeTerm [σΣ] [σt]
      [σA₊] = proj₁ ([A₊] {σ = liftSubstn σ 2} (ε ∙ ⊢F ∙ ⊢G)
                          (liftSubstS {F = G} (_∙_ {A = F} [Γ] [F]) (ε ∙ ⊢F) [G]
                                              (liftSubstS {F = F} [Γ] ε [F] [σ])))
      [σu] = proj₁ ([u] {σ = liftSubstn σ 2} (ε ∙ ⊢F ∙ ⊢G) (liftSubstS {F = G} (_∙_ {A = F} [Γ] [F]) (ε ∙ ⊢F) [G]
                                                           (liftSubstS {F = F} [Γ] ε [F] [σ])))
      ⊢u = escapeTerm [σA₊] [σu]
      ⊢u′ = PE.subst (λ A → _ ⊢ subst (liftSubstn σ 2) u ∷ A)
                     (subst-β-prodrec A σ) ⊢u
      p₁ , p₂ , q₁ , q₂ , t⇒p , v⇒q , t®v =
        ⊩ʳt [σ] (subsumption′ {l = l} σ®σ′ (≤ᶜ-trans (+ᶜ-decreasingˡ (ω ·ᶜ γ) δ)
                                                     (≤ᶜ-reflexive (·ᶜ-identityˡ γ))))
      _ , _ , ⊢p = syntacticRedTerm t⇒p
      _ , _ , _ , _ , _ , ⊢p₁ , ⊢p₂ , eq = inversion-prod ⊢p
      eq₁ , eq₂ , _ = Σ-injectivity eq
      ⊢p₁′ = conv ⊢p₁ (sym eq₁)
      ⊢p₂′ = conv ⊢p₂ (substTypeEq (sym eq₂) (refl ⊢p₁′))
      [F]′ , [p₁]′ = reducibleTerm ⊢p₁′
      [G[p₁]]′ , [p₂]′ = reducibleTerm ⊢p₂′
      [p₁] = I.irrelevanceTerm′ (PE.sym (wk-id (subst σ F))) [F]′ ([F′] id ε) [p₁]′
      [p₁]″ = I.irrelevanceTerm [F]′ [σF] [p₁]′
      [σG[p₁]] = proj₁ ([G] ε ([σ] , [p₁]″))
      [p₂]″ = I.irrelevanceTerm′ (singleSubstComp p₁ σ G) [G[p₁]]′ [σG[p₁]] [p₂]′
      p₁®q₁ , p₂®q₂ = t®v [p₁]
      p₁®q₁′ = irrelevanceTerm′ (wk-id (subst σ F)) ([F′] id ε) [σF] p₁®q₁
      p₂®q₂′ = irrelevanceTerm′ (PE.trans (PE.cong (_[ p₁ ]) (wk-lift-id (subst (liftSubst σ) G)))
                                          (singleSubstComp p₁ σ G))
                                ([G′] id ε [p₁]) (proj₁ ([G] ε ([σ] , [p₁]″))) p₂®q₂
      σ®σ′ᵤ = subsumption′ {l = l} σ®σ′ (+ᶜ-decreasingʳ (ω ·ᶜ γ) δ)
      u®w = ⊩ʳu {σ = consSubst (consSubst σ p₁) p₂}
                {σ′ = T.consSubst (T.consSubst σ′ q₁) q₂}
                (([σ] , [p₁]″) , [p₂]″) ((σ®σ′ᵤ , p₁®q₁′) , p₂®q₂′)
      prt⇒prp = prodrec-subst* {p = ω} t⇒p ⊢F ⊢G ⊢A ⊢t ⊢u′
      prt⇒prp′ = PE.subst (ε ⊢ subst σ (prodrec ω A t u) ⇒*
                             prodrec ω (subst (liftSubst σ) A)
                             (prod p₁ p₂) (subst (liftSubstn σ 2) u) ∷_)
                          (substCompProdrec A p₁ p₂ σ)
                          (conv* prt⇒prp (substTypeEq (refl ⊢A) (subset*Term t⇒p)))
      prp⇒u = redMany (prodrec-β {p = ω} ⊢F ⊢G ⊢p₁′ ⊢p₂′ ⊢A ⊢u′)
      prp⇒u′ = PE.subst₂ (ε ⊢ prodrec ω _ (prod p₁ p₂) _ ⇒*_∷_)
                         (doubleSubstComp u p₁ p₂ σ)
                         (substCompProdrec A p₁ p₂ σ) prp⇒u
      prt⇒u = prt⇒prp′ ⇨∷* prp⇒u′
      prv⇒prq = TP.prodrec-subst* {u = T.subst (T.liftSubstn σ′ 2) (erase u)} v⇒q
      prv⇒w = TP.red*concat prv⇒prq (T.trans T.prodrec-β T.refl)
      prv⇒w′ = PE.subst (_ T.⇒*_) (TP.doubleSubstComp (erase u) q₁ q₂ σ′) prv⇒w
      [σA₊]′ = proj₁ ([A₊] ε (([σ] , [p₁]″) , [p₂]″))
      prt®prv = ®-red* [σA₊]′ u®w prt⇒u prv⇒w′
  in  convTermʳ [σA₊]′ (proj₁ ([A[t]] ε [σ]))
                (PE.subst₂ (ε ⊢_≡_) (substCompProdrec A p₁ p₂ σ)
                           (PE.sym (singleSubstLift A t))
                           (sym (substTypeEq (refl ⊢A) (subset*Term t⇒p))))
                prt®prv
