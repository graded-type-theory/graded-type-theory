{-# OPTIONS --without-K  #-}
open import Definition.Modality.Erasure

open import Definition.Typed.EqualityRelation


module Erasure.LogicalRelation.Fundamental.Product {{eqrel : EqRelSet Erasure}} where
open EqRelSet {{...}}

open import Definition.Untyped Erasure as U hiding (_∷_)
open import Definition.Untyped.Properties Erasure
open import Definition.Typed Erasure
open import Definition.Typed.Properties Erasure
open import Definition.Typed.RedSteps Erasure
open import Definition.Typed.Weakening Erasure
open import Definition.Typed.Consequences.Injectivity Erasure
open import Definition.Typed.Consequences.Inversion Erasure
open import Definition.Typed.Consequences.Reduction Erasure
open import Definition.Typed.Consequences.RedSteps Erasure
open import Definition.Typed.Consequences.Substitution Erasure
open import Definition.Typed.Consequences.Syntactic Erasure

open import Definition.LogicalRelation Erasure
import Definition.LogicalRelation.Irrelevance Erasure as I
open import Definition.LogicalRelation.Fundamental Erasure
open import Definition.LogicalRelation.Fundamental.Reducibility Erasure
open import Definition.LogicalRelation.Properties.Escape Erasure
open import Definition.LogicalRelation.ShapeView Erasure
open import Definition.LogicalRelation.Substitution Erasure
open import Definition.LogicalRelation.Substitution.Properties Erasure
open import Definition.LogicalRelation.Substitution.Introductions.Pi Erasure
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst Erasure
open import Definition.LogicalRelation.Substitution.Introductions.Universe Erasure
open import Definition.LogicalRelation.Substitution.Reducibility Erasure
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
    t₁ t₂ : Term 0
    v₁ v₂ : T.Term 0
    G : Term (1+ n)
    p q : Erasure
    γ δ : Conₘ n
    σ : Subst 0 n
    σ′ : T.Subst 0 n

Σʳ : ([Γ] : ⊩ᵛ Γ) → Γ ⊢ Σ q ▷ F ▹ G ∷ U
   → ∃ λ ([U] : Γ ⊩ᵛ⟨ ¹ ⟩ U / [Γ])
   → γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ Σ q ▷ F ▹ G ∷ U / [Γ] / [U]
Σʳ [Γ] ⊢Σ = Uᵛ [Γ] , λ [σ] σ®σ′ →
  let ⊢σΣ = substitutionTerm ⊢Σ (wellformedSubst [Γ] ε [σ]) ε
  in  Uᵣ ⊢σΣ

prodʳ : ∀ {l}
      → ([Γ] : ⊩ᵛ Γ)
        ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
        ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
        ([G[t]] : Γ ⊩ᵛ⟨ l ⟩ G [ t ] / [Γ])
        ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ F / [Γ] / [F])
        ([u] : Γ ⊩ᵛ⟨ l ⟩ u ∷ G [ t ] / [Γ] / [G[t]])
        (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷ F / [Γ] / [F])
        (⊩ʳu : δ ▸ Γ ⊩ʳ⟨ l ⟩ u ∷ G [ t ] / [Γ] / [G[t]])
      → ∃ λ ([Σ] : Γ ⊩ᵛ⟨ l ⟩ Σ q ▷ F ▹ G / [Γ])
      → γ +ᶜ δ ▸ Γ ⊩ʳ⟨ l ⟩ prod t u ∷ Σ q ▷ F ▹ G / [Γ] / [Σ]
prodʳ {F = F} {G = G} {t = t} {u = u} {γ = γ} {δ = δ} {q = q} {l = l}
      [Γ] [F] [G] [G[t]] [t] [u] ⊩ʳt ⊩ʳu =
  let [Σ] = Σᵛ {F = F} {G = G} [Γ] [F] [G]
  in  [Σ] , λ {σ = σ} {σ′ = σ′} [σ] σ®σ′ →
      let σ®σ′ₜ = subsumption′ {l = l} σ®σ′ (+ᶜ-decreasingˡ γ δ)
          σ®σ′ᵤ = subsumption′ {l = l} σ®σ′ (+ᶜ-decreasingʳ γ δ)
          _  , Bᵣ F′ G′ D ⊢F ⊢G A≡A [F′] [G′] G-ext = extractMaybeEmb (Σ-elim (proj₁ ([Σ] ε [σ])))
          [σF] = proj₁ ([F] ε [σ])
          [σG[t]] = proj₁ ([G[t]] ε [σ])
          ⊢t = escapeTerm [σF] (proj₁ ([t] ε [σ]))
          ⊢u = escapeTerm [σG[t]] (proj₁ ([u] ε [σ]))
          ⊢u′ = PE.subst (λ A → ε ⊢ subst σ u ∷ A) (singleSubstLift G t) ⊢u
      in  subst σ t , subst σ u , T.subst σ′ (erase t) , T.subst σ′ (erase u)
          , id (prodⱼ ⊢F ⊢G ⊢t ⊢u′) , T.refl , λ [t₁] →
          let t®v = ⊩ʳt [σ] σ®σ′ₜ
              u®w = ⊩ʳu [σ] σ®σ′ᵤ
              t®v′ = irrelevanceTerm′ (PE.sym (wk-id (subst σ F))) [σF]  ([F′] id ε) t®v
              u®w′ = irrelevanceTerm′ (PE.trans (singleSubstLift G t)
                                                (PE.cong (_[ subst σ t ])
                                                         (PE.sym (wk-lift-id (subst (liftSubst σ) G)))))
                                      [σG[t]] ([G′] id ε [t₁]) u®w
          in t®v′ , u®w′


fstʳ′ : ∀ {l} {Γ : Con Term n}
      → ([Γ] : ⊩ᵛ Γ)
        ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
        ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
        (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷ Σ q ▷ F ▹ G / [Γ] / Σᵛ {F = F} {G = G} {q = q} [Γ] [F] [G])
      → γ ▸ Γ ⊩ʳ⟨ l ⟩ fst t ∷ F / [Γ] / [F]
fstʳ′ {F = F} {G} {t = t} {q = q} [Γ] [F] [G] ⊩ʳt {σ = σ} [σ] σ®σ′ =
  let [Σ] = Σᵛ {F = F} {G = G} {q = q} [Γ] [F] [G]
      t₁ , t₂ , v₁ , v₂ , t⇒t′ , v⇒v′ , t®v = ⊩ʳt [σ] σ®σ′
      _  , Bᵣ F′ G′ D ⊢F ⊢G A≡A [F′] [G′] G-ext = extractMaybeEmb
                                                  (Σ-elim (proj₁ ([Σ] ε [σ])))
      _ , _ , ⊢t = syntacticRedTerm t⇒t′
      _ , _ , _ , _ , _ , ⊢t₁ , ⊢t₂ , eq = inversion-prod ⊢t
      eq₁ , eq₂ , _ = Σ-injectivity eq
      ⊢t₁′ = conv ⊢t₁ (sym eq₁)
      eq₂′ = substitutionEq eq₂ (substRefl (singleSubst ⊢t₁′)) ε
      ⊢t₂′ = conv ⊢t₂ (sym eq₂′)
      t⇒u = fst-subst* t⇒t′ ⊢F ⊢G
      t⇒u′ = t⇒u ⇨∷* redMany (Σ-β₁ {q = q} ⊢F ⊢G ⊢t₁′ ⊢t₂′ (prodⱼ ⊢F ⊢G ⊢t₁′ ⊢t₂′))
      v⇒w = TP.red*concat (TP.fst-subst* v⇒v′) (T.trans T.Σ-β₁ T.refl)
      [F]′ , [t₁]′ = reducibleTerm (conv ⊢t₁ (sym eq₁))
      [t₁] = I.irrelevanceTerm′ (PE.sym (wk-id (subst σ F))) [F]′ ([F′] id ε) [t₁]′
      t₁®v₁ , _ = t®v [t₁]
      t₁®v₁′ = ®-red* ([F′] id ε) t₁®v₁
                      (PE.subst (ε ⊢ fst (subst σ t) ⇒* t₁ ∷_)
                                (PE.sym (wk-id (subst σ F))) t⇒u′)
                      v⇒w
  in  irrelevanceTerm′ (wk-id (subst σ F)) ([F′] id ε) (proj₁ ([F] ε [σ])) t₁®v₁′

fstʳ : Γ ⊢ F → Γ ∙ F ⊢ G → Γ ⊢ t ∷ Σ q ▷ F ▹ G
     → ([Γ] : ⊩ᵛ Γ) ([Σ] : Γ ⊩ᵛ⟨ ¹ ⟩ Σ q ▷ F ▹ G / [Γ])
     → (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ t ∷ Σ q ▷ F ▹ G / [Γ] / [Σ])
     → ∃ λ ([F] : Γ ⊩ᵛ⟨ ¹ ⟩ F / [Γ])
     → γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ fst t ∷ F / [Γ] / [F]
fstʳ {Γ = Γ} {F = F} {G = G} {t = t} {q = q} Γ⊢F Γ⊢G Γ⊢t:Σ [Γ] [Σ] ⊩ʳt =
  let [Γ]₁ , [F]′ = fundamental Γ⊢F
      [Γ]₂ , [G]′ = fundamental Γ⊢G
      [F] = IS.irrelevance {A = F} [Γ]₁ [Γ] [F]′
      [G] = IS.irrelevance {A = G} [Γ]₂ ([Γ] ∙ [F]) [G]′
      [Σ]′ = Σᵛ {F = F} {G = G} {q = q} [Γ] [F] [G]
      ⊩ʳt′ = irrelevance {A = Σ q ▷ F ▹ G} {t = t} [Γ] [Γ] [Σ] [Σ]′ ⊩ʳt
  in  [F] , fstʳ′ {F = F} {G = G} {t = t} {q = q} [Γ] [F] [G] ⊩ʳt′

sndʳ′ : ∀ {l} {Γ : Con Term n}
      → ([Γ] : ⊩ᵛ Γ)
        ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
        ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
        ([t₁] : Γ ⊩ᵛ⟨ l ⟩ fst t ∷ F / [Γ] / [F])
        (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷ Σ q ▷ F ▹ G / [Γ] / Σᵛ {F = F} {G = G} {q = q} [Γ] [F] [G])
      → ∃ λ ([G] : Γ ⊩ᵛ⟨ l ⟩ G [ fst t ] / [Γ])
      → γ ▸ Γ ⊩ʳ⟨ l ⟩ snd t ∷ G [ fst t ] / [Γ] / [G]
sndʳ′ {F = F} {G} {t} {q = q} [Γ] [F] [G] [t₁] ⊩ʳt =
  let [Σ] = Σᵛ {F = F} {G = G} {q = q} [Γ] [F] [G]
      [G[t₁]] = substSΠ {F = F} {G = G} {t = fst t} (BΣ q) [Γ] [F] [Σ] [t₁]
  in  [G[t₁]] , λ {σ = σ} [σ] σ®σ′ →
      let t₁ , t₂ , v₁ , v₂ , t⇒t′ , v⇒v′ , t®v = ⊩ʳt [σ] σ®σ′
          _  , Bᵣ F′ G′ D ⊢F ⊢G A≡A [F′] [G′] G-ext = extractMaybeEmb
                                                      (Σ-elim (proj₁ ([Σ] ε [σ])))
          _ , _ , ⊢t = syntacticRedTerm t⇒t′
          _ , _ , _ , _ , _ , ⊢t₁ , ⊢t₂ , eq = inversion-prod ⊢t
          eq₁ , eq₂ , _ = Σ-injectivity eq
          ⊢t₁′ = conv ⊢t₁ (sym eq₁)
          eq₂′ = substitutionEq eq₂ (substRefl (singleSubst ⊢t₁′)) ε
          ⊢t₂′ = conv ⊢t₂ (sym eq₂′)
          t≡t₁ = subset*Term (redMany (Σ-β₁ {q = q} ⊢F ⊢G ⊢t₁′ ⊢t₂′
                                            (prodⱼ ⊢F ⊢G ⊢t₁′ ⊢t₂′)))
          t′≡t₁ = subset*Term (fst-subst* t⇒t′ ⊢F ⊢G ⇨∷*
                               redMany (Σ-β₁ {q = q} ⊢F ⊢G ⊢t₁′ ⊢t₂′
                                             (prodⱼ ⊢F ⊢G ⊢t₁′ ⊢t₂′)))
          G[t]≡G[t₁] = substTypeEq (refl ⊢G) t≡t₁
          G[t]≡G[t₁]′ = PE.subst (ε ⊢ subst (liftSubst σ) G [ _ ] ≡_)
                                 (PE.cong (_[ t₁ ])
                                          (PE.sym (wk-lift-id (subst (liftSubst σ) G))))
                                 G[t]≡G[t₁]
          G[t′]≡G[t₁] = substTypeEq (refl ⊢G) t′≡t₁
          G[t′]≡G[t₁]′ = PE.subst₂ (ε ⊢_≡_)
                                   (PE.cong (_[ t₁ ])
                                            (PE.sym (wk-lift-id (subst (liftSubst σ) G))))
                                   (PE.sym (singleSubstLift G (fst t)))
                                   (sym G[t′]≡G[t₁])
          t⇒u = conv* (snd-subst* t⇒t′ ⊢F ⊢G)
                      (substTypeEq (refl ⊢G) (fst-cong ⊢F ⊢G (subset*Term t⇒t′)))
          t⇒u′ = t⇒u ⇨∷* redMany (Σ-β₂ {q = q} ⊢F ⊢G ⊢t₁′ ⊢t₂′ (prodⱼ ⊢F ⊢G ⊢t₁′ ⊢t₂′))
          t⇒u″ = conv* t⇒u′ G[t]≡G[t₁]′
          v⇒w = TP.red*concat (TP.snd-subst* v⇒v′) (T.trans T.Σ-β₂ T.refl)
          [F]′ , [t₁]′ = reducibleTerm (conv ⊢t₁ (sym eq₁))
          [t₁] = I.irrelevanceTerm′ (PE.sym (wk-id (subst σ F))) [F]′ ([F′] id ε) [t₁]′
          _ , t₂®v₂ = t®v [t₁]
          t₂®v₂′ = ®-red* ([G′] id ε [t₁]) t₂®v₂ t⇒u″ v⇒w
      in  convTermʳ ([G′] id ε [t₁]) (proj₁ ([G[t₁]] ε [σ])) G[t′]≡G[t₁]′ t₂®v₂′


sndʳ : Γ ⊢ F → Γ ∙ F ⊢ G → Γ ⊢ t ∷ Σ q ▷ F ▹ G
     → ([Γ] : ⊩ᵛ Γ) ([Σ] : Γ ⊩ᵛ⟨ ¹ ⟩ Σ q ▷ F ▹ G / [Γ])
     → (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ t ∷ Σ q ▷ F ▹ G / [Γ] / [Σ])
     → ∃ λ ([G] : Γ ⊩ᵛ⟨ ¹ ⟩ G [ fst t ] / [Γ])
     → γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ snd t ∷ G [ fst t ] / [Γ] / [G]
sndʳ {Γ = Γ} {F = F} {G = G} {t = t} {q = q} Γ⊢F Γ⊢G Γ⊢t:Σ [Γ] [Σ] ⊩ʳt =
  let [Γ]₁ , [F]′ = fundamental Γ⊢F
      [Γ]₂ , [G]′ = fundamental Γ⊢G
      [F] = IS.irrelevance {A = F} [Γ]₁ [Γ] [F]′
      [G] = IS.irrelevance {A = G} [Γ]₂ ([Γ] ∙ [F]) [G]′
      [Σ]′ = Σᵛ {F = F} {G = G} {q = q} [Γ] [F] [G]
      ⊩ʳt′ = irrelevance {A = Σ q ▷ F ▹ G} {t = t} [Γ] [Γ] [Σ] [Σ]′ ⊩ʳt
      Γ⊢t₁:F = fstⱼ Γ⊢F Γ⊢G Γ⊢t:Σ
      [Γ]₃ , [F]″ , [t₁]′ = fundamentalTerm Γ⊢t₁:F
      [t₁] = IS.irrelevanceTerm {A = F} {t = fst t} [Γ]₃ [Γ] [F]″ [F] [t₁]′
  in  sndʳ′ {F = F} {G = G} {t = t} {q = q} [Γ] [F] [G] [t₁] ⊩ʳt′
