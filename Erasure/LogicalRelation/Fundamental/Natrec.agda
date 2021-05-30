{-# OPTIONS --without-K   #-}
open import Definition.Modality.Erasure

open import Definition.Typed.EqualityRelation


module Erasure.LogicalRelation.Fundamental.Natrec {{eqrel : EqRelSet Erasure}} where
open EqRelSet {{...}}

open import Definition.Untyped Erasure as U hiding (_∷_)
open import Definition.Untyped.Properties Erasure
open import Definition.Typed Erasure
open import Definition.Typed.Properties Erasure
open import Definition.Typed.RedSteps Erasure
open import Definition.Typed.Consequences.RedSteps Erasure
-- open import Definition.Typed.Weakening Erasure
open import Definition.Typed.Consequences.Inversion Erasure
open import Definition.Typed.Consequences.Reduction Erasure
open import Definition.Typed.Consequences.Substitution Erasure
open import Definition.Typed.Consequences.Syntactic Erasure

open import Definition.LogicalRelation Erasure
import Definition.LogicalRelation.Irrelevance Erasure as I
open import Definition.LogicalRelation.Fundamental.Reducibility Erasure
open import Definition.LogicalRelation.Substitution Erasure
open import Definition.LogicalRelation.Substitution.Properties Erasure
open import Definition.LogicalRelation.Substitution.Introductions.Nat Erasure
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst Erasure
open import Definition.LogicalRelation.Properties.Escape Erasure

open import Definition.Modality.Context ErasureModality
-- open import Definition.Modality.Usage ErasureModality
open import Definition.Modality.Erasure.Properties

open import Erasure.LogicalRelation
open import Erasure.LogicalRelation.Conversion
open import Erasure.LogicalRelation.Irrelevance
open import Erasure.LogicalRelation.Properties
open import Erasure.Extraction
open import Erasure.Extraction.Properties
import Erasure.Target as T
import Erasure.Target.Properties.Reduction as TR

open import Tools.Fin
open import Tools.Nat hiding (_+_)
open import Tools.Product
open import Tools.Unit
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n
    t z m : Term n
    A : Term (1+ n)
    s : Term (1+ (1+ n))
    v w : T.Term n
    p r : Erasure
    γ δ η : Conₘ n
    σ : Subst 0 n
    σ′ : T.Subst 0 n


natrecʳ″ : ∀ {l m w} {Γ : Con Term n}
         → ([Γ] : ⊩ᵛ Γ)
           (let [ℕ] = ℕᵛ {l = l} [Γ])
           ([A] : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ [ℕ])
           ([A₊] : Γ ∙ ℕ ∙ A ⊩ᵛ⟨ l ⟩ wk1 (A [ (suc (var x0)) ]↑) / [Γ] ∙ [ℕ] ∙ [A])
           ([A₀] : Γ ⊩ᵛ⟨ l ⟩ A [ zero ] / [Γ])
           ([z] : Γ ⊩ᵛ⟨ l ⟩ z ∷ A [ zero ] / [Γ] / [A₀])
           ([s] : Γ ∙ ℕ ∙ A ⊩ᵛ⟨ l ⟩ s ∷  wk1 (A [ (suc (var x0)) ]↑) / [Γ] ∙ [ℕ] ∙ [A] / [A₊])
           ([σ] : ε ⊩ˢ σ ∷ Γ / [Γ] / ε)
         → (σ®σ′ : σ ®⟨ l ⟩ σ′ ∷ Γ ◂ γ ∧ᶜ nrᶜ (δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ γ) (δ +ᶜ p ·ᶜ η) r / [Γ] / [σ])
         → (⊩ʳz : γ ▸ Γ ⊩ʳ⟨ l ⟩ z ∷ A [ zero ] / [Γ] / [A₀])
         → (⊩ʳs : δ ∙ p ∙ r ▸ Γ ∙ ℕ ∙ A
             ⊩ʳ⟨ l ⟩ s ∷ wk1 (A [ (suc (var x0)) ]↑) / [Γ] ∙ [ℕ] ∙ [A] / [A₊])
         → ([m] : ε ⊩⟨ l ⟩ m ∷ ℕ / proj₁ ([ℕ] ε [σ]))
         → (m®w : m ® w ∷ℕ)
         → natrec p r (subst (liftSubst σ) A) (subst σ z) (subst (liftSubstn σ 2) s) m
           ®⟨ l ⟩ T.natrec (T.subst σ′ (erase z)) (T.subst (T.liftSubstn σ′ 2) (erase s)) w
           ∷ subst (consSubst σ m) A / proj₁ ([A] ε ([σ] , [m]))
natrecʳ″ {n} {A} {z} {s} {σ} {σ′} {γ} {δ} {p} {η} {r} {l} {m} {w} {Γ}
         [Γ] [A] [A₊] [A₀] [z] [s] [σ] σ®σ′ ⊩ʳz ⊩ʳs [m] (zeroᵣ m⇒zero w⇒zero) =
  let [ℕ] = ℕᵛ {l = l} [Γ]
      [σA₀] = proj₁ ([A₀] ε [σ])
      [σz] = proj₁ ([z] ε [σ])
      ⊢σz = escapeTerm [σA₀] [σz]
      ⊢σz′ = PE.subst (λ G → ε ⊢ subst σ z ∷ G) (singleSubstLift A zero) ⊢σz
      [σA] = proj₁ ([A] (ε ∙ ℕⱼ ε) (liftSubstS {F = ℕ} [Γ] ε [ℕ] [σ]))
      ⊢σA = escape [σA]
      [σA[m]] = proj₁ ([A] {σ = consSubst σ m} ε ([σ] , [m]))
      [⇑²σ] = liftSubstS {F = A} (_∙_ {A = ℕ} [Γ] [ℕ]) (ε ∙ (ℕⱼ ε)) [A]
                                 (liftSubstS {F = ℕ} [Γ] ε [ℕ] [σ])
      [σA₊] = proj₁ ([A₊] {σ = liftSubstn σ 2} (ε ∙ ℕⱼ ε ∙ ⊢σA) [⇑²σ])
      ⊢σA₊ = escape [σA₊]
      [σs] = proj₁ ([s] {σ = liftSubstn σ 2} (ε ∙ ℕⱼ ε ∙ ⊢σA) [⇑²σ])
      ⊢σs = escapeTerm [σA₊] [σs]
      ⊢σs′ = PE.subst (λ G → ε ∙ ℕ ∙ (subst (liftSubst σ) A) ⊢ subst (liftSubstn σ 2) s ∷ G)
                      (natrecSucCase σ A) ⊢σs
      A[m]≡A[0] = substTypeEq (refl ⊢σA) (subset*Term m⇒zero)
      nrm⇒nr0 = natrec-subst* {p = p} {r = r} m⇒zero ⊢σA ⊢σz′ ⊢σs′
      nrm⇒nr0′ = conv* nrm⇒nr0 A[m]≡A[0]
      nr0⇒z = natrec-zero ⊢σA ⊢σz′ ⊢σs′
      nrm⇒z = nrm⇒nr0′ ⇨∷* redMany nr0⇒z
      nrw⇒nr0 = TR.natrec-subst* {s = T.subst (T.liftSubst (T.liftSubst σ′)) (erase s)} w⇒zero
      nrw⇒z = TR.red*concat nrw⇒nr0 (T.trans T.natrec-zero T.refl)
      z®z′ = ⊩ʳz [σ] (subsumption′ {l = l} σ®σ′ (∧ᶜ-decreasingˡ γ _))
      [σA₀]′ = I.irrelevance′ (singleSubstLift A zero) [σA₀]
      z®z″ = irrelevanceTerm′ (singleSubstLift A zero) [σA₀] [σA₀]′ z®z′
      nr®nr = ®-red* [σA₀]′ z®z″ nrm⇒z nrw⇒z
      [σA₀]″ = I.irrelevance′ (singleSubstComp zero σ A) [σA₀]′
      [σA[m]]′ = I.irrelevance′ (PE.sym (singleSubstComp m σ A)) [σA[m]]
      nr®nr′ = convTermʳ [σA₀]′ [σA[m]]′ (sym A[m]≡A[0]) nr®nr
  in  irrelevanceTerm′ (singleSubstComp m σ A) [σA[m]]′ [σA[m]] nr®nr′
natrecʳ″ {n} {A} {z} {s} {σ} {σ′} {γ} {δ} {p} {η} {r} {l} {m} {w} {Γ}
         [Γ] [A] [A₊] [A₀] [z] [s] [σ] σ®σ′ ⊩ʳz ⊩ʳs [m] (sucᵣ {t′ = m′} {v′ = w′} m⇒sucm′ w⇒sucw′ m′®w′) =
  let [ℕ] = ℕᵛ {l = l} [Γ]
      σnrm = natrec p r (subst (liftSubst σ) A) (subst σ z) (subst (liftSubstn σ 2) s) m
      σnrm′ = natrec p r (subst (liftSubst σ) A) (subst σ z) (subst (liftSubstn σ 2) s) m′
      σnrw′ = T.natrec (T.subst σ′ (erase z)) (T.subst (T.liftSubstn σ′ 2) (erase s)) w′
      [σA₀] = proj₁ ([A₀] ε [σ])
      [σz] = proj₁ ([z] ε [σ])
      ⊢σz = escapeTerm [σA₀] [σz]
      ⊢σz′ = PE.subst (λ G → ε ⊢ subst σ z ∷ G) (singleSubstLift A zero) ⊢σz
      [σA] = proj₁ ([A] (ε ∙ ℕⱼ ε) (liftSubstS {F = ℕ} [Γ] ε [ℕ] [σ]))
      ⊢σA = escape [σA]
      [σA[m]] = proj₁ ([A] {σ = consSubst σ m} ε ([σ] , [m]))
      [σA[m]]′ = I.irrelevance′ (PE.sym (singleSubstComp m σ A)) [σA[m]]
      [⇑²σ] = liftSubstS {F = A} (_∙_ {A = ℕ} [Γ] [ℕ]) (ε ∙ (ℕⱼ ε)) [A]
                                 (liftSubstS {F = ℕ} [Γ] ε [ℕ] [σ])
      [σA₊] = proj₁ ([A₊] {σ = liftSubstn σ 2} (ε ∙ ℕⱼ ε ∙ ⊢σA) [⇑²σ])
      ⊢σA₊ = escape [σA₊]
      [σs] = proj₁ ([s] {σ = liftSubstn σ 2} (ε ∙ ℕⱼ ε ∙ ⊢σA) [⇑²σ])
      ⊢σs = escapeTerm [σA₊] [σs]
      ⊢σs′ = PE.subst (λ G → ε ∙ ℕ ∙ (subst (liftSubst σ) A) ⊢ subst (liftSubstn σ 2) s ∷ G)
                      (natrecSucCase σ A) ⊢σs
      ⊢sucm′ = proj₂ (proj₂ (syntacticRedTerm m⇒sucm′))
      [ℕ]′ , [sucm′]′ = reducibleTerm ⊢sucm′
      [sucm′] = I.irrelevanceTerm [ℕ]′ (proj₁ ([ℕ] ε [σ])) [sucm′]′
      ⊢m′ = proj₁ (inversion-suc ⊢sucm′)
      [ℕ]′ , [m′]′ = reducibleTerm ⊢m′
      [m′] = I.irrelevanceTerm [ℕ]′ (proj₁ ([ℕ] ε [σ])) [m′]′
      [A[m′]] = proj₁ ([A] {σ = consSubst σ m′} ε ([σ] , [m′]))
      [A[sucm′]] = proj₁ ([A] {σ = consSubst σ (suc m′)} ε ([σ] , [sucm′]))
      [A[sucm′]]′ = I.irrelevance′ (PE.sym (singleSubstComp (suc m′) σ A)) [A[sucm′]]
      ⊢nrm′ = natrecⱼ {p = p} {r = r} ⊢σA ⊢σz′ ⊢σs′ ⊢m′
      [G] , [nrm′]′ = reducibleTerm ⊢nrm′
      [nrm′] = I.irrelevanceTerm′ (singleSubstComp m′ σ A) [G] [A[m′]] [nrm′]′
      [σ₊A₊] = proj₁ ([A₊] {σ = consSubst (consSubst σ m′) σnrm′} ε (([σ] , [m′]) , [nrm′]))
      A[m]≡A[sucm′] = substTypeEq (refl ⊢σA) (subset*Term m⇒sucm′)
      nrm⇒nrsucm′ = natrec-subst* {p = p} {r = r} m⇒sucm′ ⊢σA ⊢σz′ ⊢σs′
      nrm⇒nrsucm″ = conv* nrm⇒nrsucm′ A[m]≡A[sucm′]
      nrsucm′⇒s = natrec-suc ⊢m′ ⊢σA ⊢σz′ ⊢σs′
      nrm⇒s = nrm⇒nrsucm″ ⇨∷* redMany nrsucm′⇒s
      nrw⇒nrsucw′ = TR.natrec-subst* {z = T.subst σ′ (erase z)}
                                     {s = T.subst (T.liftSubst (T.liftSubst σ′)) (erase s)}
                                     w⇒sucw′
      nrw⇒s = TR.red*concat nrw⇒nrsucw′ (T.trans T.natrec-suc T.refl)
      σ®σ′ₛ = subsumption′ {l = l} σ®σ′ (≤ᶜ-trans (∧ᶜ-decreasingʳ γ _)
                                        (≤ᶜ-trans (nrᶜ-decreasingʳ _ _ r)
                                                  (+ᶜ-decreasingˡ δ (p ·ᶜ η))))
      nrm′®nrw′ = natrecʳ″ {A = A} {z = z} {s = s} [Γ] [A] [A₊] [A₀] [z] [s] [σ] σ®σ′ ⊩ʳz ⊩ʳs [m′] m′®w′
      s®s′ = ⊩ʳs {σ = consSubst (consSubst σ m′) σnrm′}
                 {σ′ = T.consSubst (T.consSubst σ′ w′) σnrw′}
                 (([σ] , [m′]) , [nrm′])
                 ((σ®σ′ₛ , subsumption″ m′®w′ (least-elem p)) ,
                           subsumption″ nrm′®nrw′ (least-elem r))
      s®s″ = irrelevanceTerm′ {!m⇒sucm′!} [σ₊A₊] [A[sucm′]]′ s®s′
      s®s‴ = PE.subst₂ (λ t v → t ®⟨ l ⟩ v ∷ subst (liftSubst σ) A [ suc m′ ] / [A[sucm′]]′) {!!} {!!} s®s″
      nrm®nrw = ®-red* [A[sucm′]]′ s®s‴ nrm⇒s nrw⇒s
      nrm®nrw′ = convTermʳ [A[sucm′]]′ [σA[m]]′ (sym A[m]≡A[sucm′]) nrm®nrw
  in  irrelevanceTerm′ (singleSubstComp m σ A) [σA[m]]′ [σA[m]] nrm®nrw′


natrecʳ′ : ∀ {l} {Γ : Con Term n}
         → ([Γ] : ⊩ᵛ Γ)
           (let [ℕ] = ℕᵛ {l = l} [Γ])
           ([A] : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ [ℕ])
           ([A₊] : Γ ∙ ℕ ∙ A ⊩ᵛ⟨ l ⟩ wk1 (A [ (suc (var x0)) ]↑) / [Γ] ∙ [ℕ] ∙ [A])
           ([A₀] : Γ ⊩ᵛ⟨ l ⟩ A [ zero ] / [Γ])
           ([A[m]] : Γ ⊩ᵛ⟨ l ⟩ A [ m ] / [Γ])
           ([z] : Γ ⊩ᵛ⟨ l ⟩ z ∷ A [ zero ] / [Γ] / [A₀])
           ([s] : Γ ∙ ℕ ∙ A ⊩ᵛ⟨ l ⟩ s ∷  wk1 (A [ (suc (var x0)) ]↑) / [Γ] ∙ [ℕ] ∙ [A] / [A₊])
           ([m] : Γ ⊩ᵛ⟨ l ⟩ m ∷ ℕ / [Γ] / [ℕ])
         → (⊩ʳz : γ ▸ Γ ⊩ʳ⟨ l ⟩ z ∷ A [ zero ] / [Γ] / [A₀])
         → (⊩ʳs : δ ∙ p ∙ r ▸ Γ ∙ ℕ ∙ A
             ⊩ʳ⟨ l ⟩ s ∷ wk1 (A [ (suc (var x0)) ]↑) / [Γ] ∙ [ℕ] ∙ [A] / [A₊])
         → (⊩ʳm : η ▸ Γ ⊩ʳ⟨ l ⟩ m ∷ ℕ / [Γ] / [ℕ])
         → γ ∧ᶜ nrᶜ (δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ γ) (δ +ᶜ p ·ᶜ η) r ▸ Γ
             ⊩ʳ⟨ l ⟩ natrec p r A z s m ∷ A [ m ] / [Γ] / [A[m]]
natrecʳ′ {n} {A} {m} {z} {s} {γ} {δ} {𝟘} {r} {η} {l} {Γ} [Γ] [A] [A₊] [A₀] [A[m]] [z] [s] [m] ⊩ʳz ⊩ʳs ⊩ʳm {σ} {σ′} [σ] σ®σ′ =
  let [σm] = proj₁ ([m] ε [σ])
      m®w = ⊩ʳm [σ] (subsumption′ {!σ®σ′!} {!!})
      nr®nr = natrecʳ″ {A = A} {z = z} {s = s}
                       [Γ] [A] [A₊] [A₀] [z] [s] [σ] σ®σ′ ⊩ʳz ⊩ʳs [σm] m®w
  in  {!⊩ʳm [σ]!}
natrecʳ′ {n} {A} {m} {z} {s} {γ} {δ} {ω} {r} {η} {l} {Γ}
         [Γ] [A] [A₊] [A₀] [A[m]] [z] [s] [m] ⊩ʳz ⊩ʳs ⊩ʳm {σ} {σ′} [σ] σ®σ′ =
  let σ®σ′ᵐ = subsumption′ {l = l} σ®σ′ (≤ᶜ-trans (∧ᶜ-decreasingʳ γ _)
                                        (≤ᶜ-trans (nrᶜ-decreasingʳ _ _ r)
                                        (≤ᶜ-trans (+ᶜ-decreasingʳ δ (ω ·ᶜ η))
                                                  (≤ᶜ-reflexive (·ᶜ-identityˡ η)))))
      m®w = ⊩ʳm [σ] σ®σ′ᵐ
      [σm] = proj₁ ([m] ε [σ])
      nr®nr = natrecʳ″ {A = A} {z = z} {s = s}
                       [Γ] [A] [A₊] [A₀] [z] [s] [σ] σ®σ′ ⊩ʳz ⊩ʳs [σm] m®w
  in  irrelevanceTerm′ (PE.sym (PE.trans (singleSubstLift A m) (singleSubstComp (subst σ m) σ A)))
                       (proj₁ ([A] ε ([σ] , [σm]))) (proj₁ ([A[m]] ε [σ])) nr®nr

natrecʳ : ∀ {l} {Γ : Con Term n}
         → ([Γ] : ⊩ᵛ Γ)
           (let [ℕ] = ℕᵛ {l = l} [Γ])
           ([A] : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ [ℕ])
           ([A₊] : Γ ∙ ℕ ∙ A ⊩ᵛ⟨ l ⟩ wk1 (A [ (suc (var x0)) ]↑) / [Γ] ∙ [ℕ] ∙ [A])
           ([A₀] : Γ ⊩ᵛ⟨ l ⟩ A [ zero ] / [Γ])
           ([z] : Γ ⊩ᵛ⟨ l ⟩ z ∷ A [ zero ] / [Γ] / [A₀])
           ([s] : Γ ∙ ℕ ∙ A ⊩ᵛ⟨ l ⟩ s ∷  wk1 (A [ (suc (var x0)) ]↑) / [Γ] ∙ [ℕ] ∙ [A] / [A₊])
           ([m] : Γ ⊩ᵛ⟨ l ⟩ m ∷ ℕ / [Γ] / [ℕ])
         → (⊩ʳz : γ ▸ Γ ⊩ʳ⟨ l ⟩ z ∷ A [ zero ] / [Γ] / [A₀])
         → (⊩ʳs : δ ∙ p ∙ r ▸ Γ ∙ ℕ ∙ A
             ⊩ʳ⟨ l ⟩ s ∷ wk1 (A [ (suc (var x0)) ]↑) / [Γ] ∙ [ℕ] ∙ [A] / [A₊])
         → (⊩ʳm : η ▸ Γ ⊩ʳ⟨ l ⟩ m ∷ ℕ / [Γ] / [ℕ])
         → ∃ λ ([A[m]] : Γ ⊩ᵛ⟨ l ⟩ A [ m ] / [Γ])
         → γ ∧ᶜ nrᶜ (δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ γ) (δ +ᶜ p ·ᶜ η) r ▸ Γ
             ⊩ʳ⟨ l ⟩ natrec p r A z s m ∷ A [ m ] / [Γ] / [A[m]]
natrecʳ {n} {A} {z} {s} {m} {γ} {δ} {p} {r} {η} {l} {Γ}
        [Γ] [A] [A₊] [A₀] [z] [s] [m] ⊩ʳz ⊩ʳs ⊩ʳm =
  let [A[m]] = substS {F = ℕ} {G = A}  [Γ] (ℕᵛ [Γ]) [A] [m]
  in  [A[m]] , natrecʳ′ {A = A} {m = m} {z = z} {s = s} [Γ] [A] [A₊] [A₀] [A[m]] [z] [s] [m] ⊩ʳz ⊩ʳs ⊩ʳm





  -- let A′ = subst (liftSubst σ) A
  --     z′ = subst σ z
  --     s′ = subst (liftSubst (liftSubst σ)) s
  --     -- m′ = subst σ m
  --     -- [Aₘ]′ = proj₁ ([Aₘ] ε [σ])
  --     [A₀]′ = proj₁ ([A₀] ε [σ])
  --     [ℕ] = ℕᵛ {l = l} [Γ]
  --     ⊢ℕ = escape (proj₁ ([ℕ] ε [σ]))
  --     ⊢A′ = escape (proj₁ ([A] {σ = liftSubst σ} (ε ∙ ⊢ℕ) (liftSubstS {F = ℕ} [Γ] ε [ℕ] [σ])))
  --     [⇑⇑σ] = liftSubstS {σ = liftSubst σ} {F = A} (_∙_ {A = ℕ} [Γ] [ℕ]) (ε ∙ ⊢ℕ) [A]
  --                        (liftSubstS {F = ℕ} [Γ] ε [ℕ] [σ])
  --     Γ₊ = ε ∙ ℕ ∙ subst (liftSubst σ) A
  --     -- σ′ = consSubst σ m'
  --     [A₊]′ : Γ₊ ⊩⟨ l ⟩ subst (liftSubst (liftSubst σ)) (wk1 (A [ suc (var x0) ]↑))
  --     [A₊]′ = {! proj₁ ([A₊] {σ = ?} ε ?) !} -- ([σ] , [m'] , ?)

  --     -- [A₊]′ : Γ₊ ⊩⟨ l ⟩ subst (liftSubst (liftSubst σ)) (wk1 (A [ suc (var x0) ]↑))
  --     -- [A₊]′ = proj₁ ([A₊] {σ = liftSubst (liftSubst σ)} (ε ∙ ⊢ℕ ∙ ⊢A′) [⇑⇑σ])
  --     -- [A₊]″ : ε ⊩⟨ l ⟩ subst (liftSubst σ) A [ suc m' ]
  --     [A₊]″ = {![A₊]′!} -- {!PE.subst (λ □ → Γ₊ ⊩⟨ l ⟩ □) {! (natrecSucCase σ A) !} [A₊]′!}
  --        -- singleSubstLift↑
  --     ⊢z′ = escapeTerm [A₀]′ (proj₁ ([z] ε [σ]))
  --     ⊢z″ = PE.subst (λ A → ε ⊢ subst σ z ∷ A)
  --                    (PE.trans (PE.sym (substConsId A))
  --                              (PE.sym (singleSubstComp zero σ A)))
  --                    ⊢z′
  --     ⊢s′ = escapeTerm [A₊]′ (proj₁ ([s] (ε ∙ ⊢ℕ ∙ ⊢A′) [⇑⇑σ]))
  --     -- m′≡succ = subset*Term (redₜ d)
  --     ⊩ʳnr = natrecʳ′ [Γ] [A] [A₊] [A₀] [z] [s] [σ] σ®σ′ ⊩ʳz ⊩ʳs {!!}
  --     σ®σ′ᵐ = subsumption′ σ®σ′ (≤ᶜ-trans (∧ᶜ-decreasingʳ γ _)
  --                               (≤ᶜ-trans (nrᶜ-decreasingʳ _ _ r)
  --                               (≤ᶜ-trans (+ᶜ-decreasingʳ δ (p ·ᶜ η)) {!!})))
  --     σ®σ′ˢ = subsumption′ σ®σ′ (≤ᶜ-trans (∧ᶜ-decreasingʳ γ _)
  --                               (≤ᶜ-trans (nrᶜ-decreasingʳ _ _ r) (+ᶜ-decreasingˡ δ (p ·ᶜ η))))
  --     -- m®w = ⊩ʳm [σ] σ®σ′ᵐ
  --     s®v = ⊩ʳs {!!} ((σ®σ′ˢ , {!m®w!}) , {!!})
  -- in  ®-red₁ [A₊]″ {!⊩ʳs {! [σ] , [m'] , ? !} {! σ®σ′ !} !} (natrec-suc {!!} ⊢A′ ⊢z″ {!!}) T.natrec-suc

         -- → subst σ (natrec p r A z s m) ®⟨ l ⟩ T.subst σ′ (erase (natrec p r A z s m)) ∷ subst σ (A [ m ]) / proj₁ ([Aₘ] ε [σ])

{-
natrecʳ′ : ∀ {l} {Γ : Con Term n}
         → ([Γ] : ⊩ᵛ Γ)
           ([ℕ] : Γ ⊩ᵛ⟨ l ⟩ ℕ / [Γ])
           ([A] : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ [ℕ])
           ([A₊] : Γ ∙ ℕ ∙ A ⊩ᵛ⟨ l ⟩ wk1 (A [ (suc (var x0)) ]↑) / [Γ] ∙ [ℕ] ∙ [A])
           ([A₀] : Γ ⊩ᵛ⟨ l ⟩ A [ zero ] / [Γ])
           ([Aₘ] : Γ ⊩ᵛ⟨ l ⟩ A [ m ] / [Γ])
           ([z] : Γ ⊩ᵛ⟨ l ⟩ z ∷ A [ zero ] / [Γ] / [A₀])
           ([s] : Γ ∙ ℕ ∙ A ⊩ᵛ⟨ l ⟩ s ∷  wk1 (A [ (suc (var x0)) ]↑) / [Γ] ∙ [ℕ] ∙ [A] / [A₊])
           ([m] : Γ ⊩ᵛ⟨ l ⟩ m ∷ ℕ / [Γ] / [ℕ])
           ([σ] : ε ⊩ˢ σ ∷ Γ / [Γ] / ε)
         → σ ®⟨ l ⟩ σ′ ∷ Γ ◂ γ ∧ᶜ nrᶜ (δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ η) (δ +ᶜ p ·ᶜ η) r / [Γ] / [σ]
         → γ ▸ Γ ⊩ʳ⟨ l ⟩ z ∷ A [ zero ] / [Γ] / [A₀]
         → δ ∙ p ∙ r ▸ Γ ∙ ℕ ∙ A
             ⊩ʳ⟨ l ⟩ s ∷ wk1 (A [ (suc (var x0)) ]↑) / [Γ] ∙ [ℕ] ∙ [A] / [A₊]
         → η ▸ Γ ⊩ʳ⟨ l ⟩ m ∷ ℕ / [Γ] / [ℕ]
         → ε ⊩ℕ subst σ m ∷ℕ
         → subst σ (natrec p r A z s m) ®⟨ l ⟩ T.subst σ′ (erase (natrec p r A z s m)) ∷ subst σ (A [ m ]) / proj₁ ([Aₘ] ε [σ])
natrecʳ′ {A = A} {m} {z} {s} {σ = σ} {σ′ = σ′} {γ = γ} {δ} {p} {η} {r}
         [Γ] [ℕ] [A] [A₊] [A₀] [Aₘ] [z] [s] [m] [σ] σ®σ′ ⊩ʳz ⊩ʳs ⊩ʳm (ℕₜ n d n≡n (sucᵣ x)) =
  let A′ = subst (liftSubst σ) A
      z′ = subst σ z
      s′ = subst (liftSubst (liftSubst σ)) s
      m′ = subst σ m
      [Aₘ]′ = proj₁ ([Aₘ] ε [σ])
      [A₀]′ = proj₁ ([A₀] ε [σ])
      ⊢ℕ = escape (proj₁ ([ℕ] ε [σ]))
      ⊢A′ = escape (proj₁ ([A] {σ = liftSubst σ} (ε ∙ ⊢ℕ) (liftSubstS {F = ℕ} [Γ] ε [ℕ] [σ])))
      [⇑⇑σ] = liftSubstS {σ = liftSubst σ} {F = A} (_∙_ {A = ℕ} [Γ] [ℕ]) (ε ∙ ⊢ℕ) [A]
                         (liftSubstS {F = ℕ} [Γ] ε [ℕ] [σ])
      [A₊]′ = proj₁ ([A₊] {σ = liftSubst (liftSubst σ)} (ε ∙ ⊢ℕ ∙ ⊢A′) [⇑⇑σ])
      ⊢z′ = escapeTerm [A₀]′ (proj₁ ([z] ε [σ]))
      ⊢z″ = PE.subst (λ A → ε ⊢ subst σ z ∷ A)
                     (PE.trans (PE.sym (substConsId A))
                               (PE.sym (singleSubstComp zero σ A)))
                     ⊢z′
      ⊢s′ = escapeTerm [A₊]′ (proj₁ ([s] (ε ∙ ⊢ℕ ∙ ⊢A′) [⇑⇑σ]))
      m′≡succ = subset*Term (redₜ d)
      ⊩ʳnr = natrecʳ′ [Γ] [ℕ] [A] [A₊] [A₀] {![Aₘ]!} [z] [s] {!!} [σ] σ®σ′ ⊩ʳz ⊩ʳs {!!} {!x!}
      σ®σ′ᵐ = subsumption′ σ®σ′ (≤ᶜ-trans (∧ᶜ-decreasingʳ γ _)
                                (≤ᶜ-trans (nrᶜ-decreasingʳ _ _ r)
                                (≤ᶜ-trans (+ᶜ-decreasingʳ δ (p ·ᶜ η)) {!!})))
      σ®σ′ˢ = subsumption′ σ®σ′ (≤ᶜ-trans (∧ᶜ-decreasingʳ γ _)
                                (≤ᶜ-trans (nrᶜ-decreasingʳ _ _ r) (+ᶜ-decreasingˡ δ (p ·ᶜ η))))
      m®w = ⊩ʳm [σ] σ®σ′ᵐ
      s®v = ⊩ʳs {!!} ((σ®σ′ˢ , {!m®w!}) , {!!})
  in  {!x!}
natrecʳ′ {A = A} {m} {z} {s} {σ = σ} {σ′ = σ′} {γ = γ} {δ} {p} {η} {r}
         [Γ] [ℕ] [A] [A₊] [A₀] [Aₘ] [z] [s] [m] [σ] σ®σ′ ⊩ʳz ⊩ʳs ⊩ʳm (ℕₜ n d n≡n zeroᵣ) =
  let A′ = subst (liftSubst σ) A
      z′ = subst σ z
      s′ = subst (liftSubst (liftSubst σ)) s
      m′ = subst σ m
      [Aₘ]′ = proj₁ ([Aₘ] ε [σ])
      [A₀]′ = proj₁ ([A₀] ε [σ])
      ⊢ℕ = escape (proj₁ ([ℕ] ε [σ]))
      ⊢A′ = escape (proj₁ ([A] {σ = liftSubst σ} (ε ∙ ⊢ℕ) (liftSubstS {F = ℕ} [Γ] ε [ℕ] [σ])))
      [⇑⇑σ] = liftSubstS {σ = liftSubst σ} {F = A} (_∙_ {A = ℕ} [Γ] [ℕ]) (ε ∙ ⊢ℕ) [A]
                         (liftSubstS {F = ℕ} [Γ] ε [ℕ] [σ])
      [A₊]′ = proj₁ ([A₊] {σ = liftSubst (liftSubst σ)} (ε ∙ ⊢ℕ ∙ ⊢A′) [⇑⇑σ])
      ⊢z′ = escapeTerm [A₀]′ (proj₁ ([z] ε [σ]))
      ⊢z″ = PE.subst (λ A → ε ⊢ subst σ z ∷ A)
                     (PE.trans (PE.sym (substConsId A))
                               (PE.sym (singleSubstComp zero σ A)))
                     ⊢z′
      ⊢s′ = escapeTerm [A₊]′ (proj₁ ([s] (ε ∙ ⊢ℕ ∙ ⊢A′) [⇑⇑σ]))
      m′≡zero = subset*Term (redₜ d)
      A[m]≡A[0] = substTypeEq (refl ⊢A′) m′≡zero
      A[m]≡A[0]′ = PE.subst (λ x → ε ⊢ x ≡ subst (liftSubst σ) A [ zero ])
                            (PE.trans (singleSubstComp (subst σ m) σ A) (substConsId A))
                            A[m]≡A[0]
      Aₘ′≡Aₘ″ = PE.trans (PE.sym (substConsId A)) (PE.sym (singleSubstComp (subst σ m) σ A))
      A₀′≡A₀″ = PE.trans (PE.sym (substConsId A)) (PE.sym (singleSubstComp zero σ A))
      [Aₘ]″ = I.irrelevance′ Aₘ′≡Aₘ″ [Aₘ]′
      [A₀]″ = I.irrelevance′ A₀′≡A₀″ [A₀]′
      σ®σ′ᶻ = subsumption′ σ®σ′ (∧ᶜ-decreasingˡ γ _)
      σ®σ′ᵐ = subsumption′ σ®σ′ (≤ᶜ-trans (∧ᶜ-decreasingʳ γ _)
                                (≤ᶜ-trans (nrᶜ-decreasingʳ _ _ r)
                                (≤ᶜ-trans (+ᶜ-decreasingʳ δ (p ·ᶜ η)) {!!})))
      z®v = ⊩ʳz [σ] σ®σ′ᶻ
      z®v′ = irrelevanceTerm′ A₀′≡A₀″ [A₀]′ [A₀]″ z®v
      m®w = ⊩ʳm [σ] σ®σ′ᵐ
      m®w′ = irrelevanceTerm (proj₁ ([ℕ] ε [σ])) (proj₁ (ℕᵛ [Γ] ε [σ])) m®w
      nr⇒z : ε ⊢ natrec p r A′ z′ s′ m′ ⇒* subst σ z ∷ A′ [ zero ]
      nr⇒z = {!natrec-subst!} ⇨ redMany (natrec-zero ⊢A′ ⊢z″ {!!})
      nr⇒v : T.natrec (T.subst σ′ (erase z)) (T.subst (T.liftSubst (T.liftSubst σ′)) (erase s)) (T.subst σ′ (erase m)) T.⇒* T.subst σ′ (erase z)
      nr⇒v = red*concat (natrec-subst* (zeroCaseRed m®w′ (redₜ d))) (T.trans T.natrec-zero T.refl)
      z®v″ = ®-red* [A₀]″ z®v′ nr⇒z nr⇒v
  in  convTermʳ [A₀]″ [Aₘ]′ (sym A[m]≡A[0]′) z®v″
natrecʳ′ [Γ] [ℕ] [A] [A₊] [A₀] [Aₘ] [z] [s] [m] [σ] σ®σ′ ⊩ʳz ⊩ʳs ⊩ʳm
         (ℕₜ n d n≡n (ne (neNfₜ neK ⊢k k≡k))) = PE.⊥-elim (noClosedNe neK)

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
