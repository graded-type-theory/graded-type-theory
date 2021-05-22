{-# OPTIONS --without-K  #-}
open import Definition.Modality.Erasure

open import Definition.Typed.EqualityRelation


module Erasure.LogicalRelation.Fundamental.Product {{eqrel : EqRelSet Erasure}} where
open EqRelSet {{...}}

open import Definition.Untyped Erasure as U hiding (_∷_)
open import Definition.Untyped.Properties Erasure
open import Definition.Typed Erasure
open import Definition.Typed.Properties Erasure
open import Definition.Typed.Weakening Erasure
open import Definition.Typed.Consequences.Reduction Erasure
open import Definition.Typed.Consequences.Substitution Erasure

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
open import Definition.LogicalRelation.Substitution.Introductions.Universe Erasure
open import Definition.LogicalRelation.Substitution.Reducibility Erasure
import Definition.LogicalRelation.Substitution.Irrelevance Erasure as IS

open import Definition.Modality.Context ErasureModality
open import Definition.Modality.Usage ErasureModality
open import Definition.Modality.Erasure.Properties

open import Erasure.LogicalRelation
open import Erasure.LogicalRelation.Properties
open import Erasure.LogicalRelation.Irrelevance

open import Erasure.Extraction
import Erasure.Target as T

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n
    F t u : Term n
    G : Term (1+ n)
    q : Erasure
    γ δ : Conₘ n

Σʳ : ([Γ] : ⊩ᵛ Γ) → Γ ⊢ Σ q ▷ F ▹ G ∷ U
   → ∃ λ ([U] : Γ ⊩ᵛ⟨ ¹ ⟩ U / [Γ])
   → γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ Σ q ▷ F ▹ G ∷ U / [Γ] / [U]
Σʳ [Γ] ⊢Σ = Uᵛ [Γ] , λ [σ] σ®σ′ →
  let ⊢σΣ = substitutionTerm ⊢Σ (wellformedSubst [Γ] ε [σ]) ε
  in  Uᵣ ⊢σΣ T.refl

prodʳ : ([Γ] : ⊩ᵛ Γ) ([F] : Γ ⊩ᵛ⟨ ¹ ⟩ F / [Γ]) ([G] : Γ ∙ F ⊩ᵛ⟨ ¹ ⟩ G / [Γ] ∙ [F])
        ([G[t]] : Γ ⊩ᵛ⟨ ¹ ⟩ G [ t ] / [Γ]) ([t] : Γ ⊩ᵛ⟨ ¹ ⟩ t ∷ F / [Γ] / [F])
        ([u] : Γ ⊩ᵛ⟨ ¹ ⟩ u ∷ G [ t ] / [Γ] / [G[t]])
        (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ t ∷ F / [Γ] / [F])
        (⊩ʳu : δ ▸ Γ ⊩ʳ⟨ ¹ ⟩ u ∷ G [ t ] / [Γ] / [G[t]])
      → ∃ λ ([Σ] : Γ ⊩ᵛ⟨ ¹ ⟩ Σ q ▷ F ▹ G / [Γ])
      → γ +ᶜ δ ▸ Γ ⊩ʳ⟨ ¹ ⟩ prod t u ∷ Σ q ▷ F ▹ G / [Γ] / [Σ]
prodʳ {F = F} {G = G} {t = t} {u = u} {γ = γ} {δ = δ} {q = q} [Γ] [F] [G] [G[t]] [t] [u] ⊩ʳt ⊩ʳu =
  let [Σ] = Σᵛ {F = F} {G = G} [Γ] [F] [G]
  in  [Σ] , λ {σ = σ} {σ′ = σ′} [σ] σ®σ′ [t₁] →
      let σt®σv = ⊩ʳt [σ] (subsumption′ {l = ¹} σ®σ′ (+ᶜ-decreasingˡ γ δ))
          σu®σw = ⊩ʳu [σ] (subsumption′ {l = ¹} σ®σ′ (+ᶜ-decreasingʳ γ δ))
          [σF] = proj₁ ([F] ε [σ])
          ⊢σF = escape [σF]
          [ρσF] = W.wk id ε [σF]
          ⊢ρσF = escape [ρσF]
          [Γ]₀ , [ρσF]′ = fundamental ⊢ρσF
          [ρσF]″ = IS.irrelevance {A = U.wk id (subst σ F)} [Γ]₀ ε [ρσF]′
          [σG] = proj₁ ([G] {σ = liftSubst σ} (ε ∙ ⊢σF) (liftSubstS {F = F} [Γ] ε [F] [σ]))
          ⊢σG = escape [σG]
          [ρσG] = W.wk (lift id) (ε ∙ ⊢ρσF) [σG]
          ⊢ρσG = escape [ρσG]
          [Γ]₁ , [ρσG]′ = fundamental ⊢ρσG
          [ρσG]″ = IS.irrelevance {A = U.wk (lift id) (subst (liftSubst σ) G)} [Γ]₁ (ε ∙ [ρσF]″) [ρσG]′
          [σG[t]]′ = proj₁ ([G[t]] ε [σ])
          [σG[t]] = I.irrelevance′ (singleSubstLift G t) [σG[t]]′
          [σt] = proj₁ ([t] ε [σ])
          ⊢σt = escapeTerm [σF] [σt]
          [σu]′ = proj₁ ([u] ε [σ])
          [σu] = I.irrelevanceTerm′ (singleSubstLift G t) [σG[t]]′ [σG[t]] [σu]′
          ⊢σu = escapeTerm [σG[t]] [σu]
          ⊢σp = prodⱼ ⊢σF ⊢σG ⊢σt ⊢σu
          ⊢σp₁ = fstⱼ ⊢σF ⊢σG ⊢σp
          [Γ]₂ , [σp₁] = reducibleTerm ⊢σp₁
          t⇒t′ = redMany (Σ-β₁ {q = q} ⊢σF ⊢σG ⊢σt ⊢σu ⊢σp)
          v⇒v′ = T.trans (T.Σ-β₁ {t = T.subst σ′ (erase t)} {u = T.subst σ′ (erase u)}) T.refl
          p₁®q₁ = ®-back-closure [σF] σt®σv t⇒t′ v⇒v′
          [G[p₁]] = {!!}
          -- I.irrelevance′ {!!} (proj₁ ([G[t]] ε [σ]))
          u⇒u′ = redMany (Σ-β₂ {q = q} ⊢σF ⊢σG ⊢σt ⊢σu ⊢σp)
          w⇒w′ = T.trans (T.Σ-β₂ {t = T.subst σ′ (erase t)} {u = T.subst σ′ (erase u)}) T.refl
          σu®σw′ = irrelevanceTerm′ {!u⇒u′!} [σG[t]]′ [G[p₁]] σu®σw
          p₂®q₂ = ®-back-closure [G[p₁]] σu®σw′ u⇒u′ w⇒w′
      in  irrelevanceTerm′ (PE.sym (wk-id (subst σ F))) [σF] [ρσF] p₁®q₁
        , {!p₂®q₂!}
--         irrelevanceTerm′ {t = snd (subst σ t)} {v = T.snd (T.subst σ′ (erase t))}
--                            (PE.sym (PE.cong (_[ fst (prod (subst σ t) (subst σ u)) ])
--                                             (wk-lift-id (subst (liftSubst σ) G))))
--                            [G[p₁]]
--                            (proj₁ ([ρσG]″ {σ = sgSubst (fst (prod (subst σ t) (subst σ u)))} ε (idSubstS ε , {!!})))
--                            p₂®q₂



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
      Γ⊢t₁:F = fstⱼ Γ⊢F Γ⊢G Γ⊢t:Σ
  in  [F] , λ [σ] σ®σ′ →
      let t®v∷Σ = ⊩ʳt′ [σ] σ®σ′
          [σF] = proj₁ ([F] ε [σ])
          [ρσF] = W.wk id ε [σF]
          [Γ]₃ , [F]″ , [t₁]‴ = fundamentalTerm Γ⊢t₁:F
          [t₁]″ = IS.irrelevanceTerm {A = F} {t = fst t} [Γ]₃ [Γ] [F]″ [F] [t₁]‴
          [t₁]′ = proj₁ ([t₁]″ ε [σ])
          [t₁] = I.irrelevanceTerm′ (PE.sym (wk-id (subst _ F))) [σF] [ρσF] [t₁]′
          t₁®v₁ = proj₁ (t®v∷Σ [t₁])
      in  irrelevanceTerm′ (wk-id (subst _ F)) [ρσF] [σF] t₁®v₁


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
      ⊢Γ = wf Γ⊢F
      Γ⊢t₁:F = fstⱼ Γ⊢F Γ⊢G Γ⊢t:Σ
      [Γfst] , [Ffst] , [fstt] = fundamentalTerm Γ⊢t₁:F
      [fstt]′ = IS.irrelevanceTerm {A = F} {t = fst t} [Γfst] [Γ] [Ffst] [F] [fstt]
      Γ⊢G[fstt] = substitution Γ⊢G (singleSubst Γ⊢t₁:F) ⊢Γ
      [Γ]₃ , [G[fstt]]′ = fundamental Γ⊢G[fstt]
      [G[fstt]] = IS.irrelevance {A = G [ fst t ]} [Γ]₃ [Γ] [G[fstt]]′
  in  [G[fstt]] , λ {σ = σ} [σ] σ®σ′ →
      let t®v∷Σ = ⊩ʳt′ [σ] σ®σ′
          _  , Bᵣ F′ G′ D ⊢F ⊢G A≡A [ρF] [ρG] G-ext = extractMaybeEmb (Σ-elim (proj₁ ([Σ] ε [σ])))
          [σF] = proj₁ ([F] ε [σ])
          ⊢σF = escape [σF]
          [ρσF] = W.wk id ε [σF]
          ⊢ρσF = escape [ρσF]
          [ε] , [ρσF]′ = fundamental ⊢ρσF
          [ρσF]″ = IS.irrelevance {A = U.wk id (subst σ F)} [ε] ε [ρσF]′
          [σfstt] = proj₁ ([fstt]′ ε [σ])
          ⊢σfstt = escapeTerm [σF] [σfstt]
          [ρσfstt] = W.wkTerm id ε [σF] [σfstt]
          ⊢ρσfstt = escapeTerm [ρσF] [ρσfstt]
          [σG] = proj₁ ([G] {σ = liftSubst σ} (ε ∙ ⊢σF)
                            (liftSubstS {σ = σ} {F = F} [Γ] ε [F] [σ]))
          [ρσG] = W.wk (lift id) (ε ∙ ⊢ρσF) [σG]
          ⊢ρσG = escape [ρσG]
          [Γ]₄ , [ρσG]′ = fundamental ⊢ρσG
          [σG[fstt]] = proj₁ ([G[fstt]] ε [σ])
          [σG[fstt]]′ = I.irrelevance′ (singleSubstLift G (fst t)) [σG[fstt]]
          ⊢ρσG[fstt]′ = substitution ⊢ρσG (singleSubst ⊢ρσfstt) ε
          ⊢ρσG[fstt] = PE.subst (λ t → ε ⊢ U.wk (lift id) (subst (liftSubst σ) G) [ t ])
                                (wk-id (subst σ (fst t))) ⊢ρσG[fstt]′
          [ρσG[fstt]] = reducible ⊢ρσG[fstt]
          [Γ]₅ , [F]″ , [t₁]‴ = fundamentalTerm Γ⊢t₁:F
          [t₁]″ = IS.irrelevanceTerm {A = F} {t = fst t} [Γ]₅ [Γ] [F]″ [F] [t₁]‴
          [t₁]′ = proj₁ ([t₁]″ ε [σ])
          [t₁] = I.irrelevanceTerm′ (PE.sym (wk-id (subst _ F))) [σF] [ρσF] [t₁]′
          t₂®v₂′ = proj₂ (t®v∷Σ [t₁])
          -- eq : U.wk (lift id) (subst (liftSubst σ) G) [ fst (subst σ t) ] PE.≡ subst σ (G [ fst t ])
          -- eq = PE.trans (PE.cong (_[ fst (subst σ t) ])
          --                        (wk-lift-id (subst (liftSubst σ) G)))
          --               (PE.sym (singleSubstLift G (fst t)))
          -- t₂®v₂ = irrelevanceTerm′ (PE.sym eq) {![σG[fstt]]!} [ρσG[fstt]] t₂®v₂′
                -- ((PE.cong (_[ fst (subst σ t) ]) (wk-lift-id (subst (liftSubst σ) G))))
                   --                {![ρσG[fstt]]!} [σG[fstt]]′ t₂®v₂′
          -- t₂®v₂ = irrelevanceTerm′ ((PE.cong (_[ fst (subst σ t) ])) (wk-lift-id (subst _ G))) [ρσG[fstt]] [σG[fstt]]′  t₂®v₂′
      in  ?
      -- irrelevanceTerm′ {!!} {![ρG] ? ? ?!} {!!} t₂®v₂′
      -- irrelevanceTerm′ (PE.sym (singleSubstLift G (fst t))) [σG[fstt]]′ [σG[fstt]] t₂®v₂
      -- irrelevanceTerm′ {!!} {!!} {!!} t₂®v₂′
      -- irrelevanceTerm′ (singleSubstLift G (fst t)) {![!} {![σG[fstt]]′!} t₂®v₂
      -- irrelevanceTerm′ {!!} {!!} {!!} t₂®v₂
      -- irrelevanceTerm′ {!!} {![G]!} {![σG]!} t₂®v₂
      -- irrelevanceTerm′ (wk-id (subst _ F)) [ρσF] [σF] t₁®v₁


-- snd (subst σ t) ®⟨ ¹ ⟩
--       Erasure.Target.Term.snd
--       (Erasure.Target.subst σ′ (Erasure.Extraction.erase t))
--       ∷
--       U.wk (lift id)
--       (subst (liftSubst σ) G)
--       [ fst (subst σ t) ]


-- gen Sndkind (subst σ t U.∷ []) ®⟨ ¹ ⟩
--       Erasure.Target.Term.snd
--       (Erasure.Target.subst σ′ (Erasure.Extraction.erase t))
--       ∷
--       U.wk
--       (lift id)
--       (subst (liftSubst σ) G)
--       [ fst (subst σ t) ]



-- -- U.wk (lift id)
-- --       (subst (liftSubst σ) G)
-- --       [ fst (subst σ t) ]

-- -- (subst (liftSubst σ) G)
-- --       [ fst (subst σ t) ]

-- -- subst σ (G [ fst t ])
-- -- --
