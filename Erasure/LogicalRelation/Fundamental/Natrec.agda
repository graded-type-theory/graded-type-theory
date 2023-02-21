open import Definition.Modality.Instances.Erasure
open import Definition.Modality.Restrictions
open import Definition.Typed.EqualityRelation

module Erasure.LogicalRelation.Fundamental.Natrec
  (restrictions : Restrictions Erasure′)
  {{eqrel : EqRelSet Erasure′}}
  where

open EqRelSet {{...}}

open import Definition.Untyped Erasure as U hiding (_∷_)
open import Definition.Untyped.Properties Erasure
open import Definition.Typed Erasure′
open import Definition.Typed.Properties Erasure′
open import Definition.Typed.RedSteps Erasure′
open import Definition.Typed.Consequences.RedSteps Erasure′
open import Definition.Typed.Consequences.Inversion Erasure′
open import Definition.Typed.Consequences.Reduction Erasure′
open import Definition.Typed.Consequences.Substitution Erasure′
open import Definition.Typed.Consequences.Syntactic Erasure′

open import Definition.LogicalRelation Erasure′
open import Definition.LogicalRelation.Fundamental.Reducibility Erasure′
open import Definition.LogicalRelation.Substitution Erasure′
open import Definition.LogicalRelation.Substitution.Properties Erasure′
open import Definition.LogicalRelation.Substitution.Introductions.Nat Erasure′
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst Erasure′
open import Definition.LogicalRelation.Properties.Escape Erasure′

import Definition.LogicalRelation.Irrelevance Erasure′ as I

open import Definition.Modality.Instances.Erasure.Modality restrictions
open import Definition.Modality.Context ErasureModality
open import Definition.Modality.Instances.Erasure.Properties
  restrictions
open import Definition.Mode ErasureModality

open import Erasure.LogicalRelation restrictions
open import Erasure.LogicalRelation.Conversion restrictions
open import Erasure.LogicalRelation.Irrelevance restrictions
open import Erasure.LogicalRelation.Subsumption restrictions
open import Erasure.LogicalRelation.Reduction restrictions
open import Erasure.Extraction
import Erasure.Target as T
import Erasure.Target.Properties as TP

open import Tools.Fin
open import Tools.Nat hiding (_+_)
open import Tools.Product
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
    mo : Mode

natrecʳ″ : ∀ {l m w} {Γ : Con Term n}
         → ([Γ] : ⊩ᵛ Γ)
           (let [ℕ] = ℕᵛ {l = l} [Γ])
           ([A] : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ [ℕ])
           ([A₊] : Γ ∙ ℕ ∙ A ⊩ᵛ⟨ l ⟩ wk1 (A [ (suc (var x0)) ]↑) / [Γ] ∙ [ℕ] ∙ [A])
           ([A₀] : Γ ⊩ᵛ⟨ l ⟩ A [ zero ] / [Γ])
           ([z] : Γ ⊩ᵛ⟨ l ⟩ z ∷ A [ zero ] / [Γ] / [A₀])
           ([s] : Γ ∙ ℕ ∙ A ⊩ᵛ⟨ l ⟩ s ∷  wk1 (A [ (suc (var x0)) ]↑) / [Γ] ∙ [ℕ] ∙ [A] / [A₊])
           ([σ] : ε ⊩ˢ σ ∷ Γ / [Γ] / ε)
         → (σ®σ′ : σ ®⟨ l ⟩ σ′ ∷[ mo ] Γ ◂ (γ ∧ᶜ η) ⊛ᶜ (δ +ᶜ p ·ᶜ η) ▷ r
                   / [Γ] / [σ])
         → (⊩ʳz : γ ▸ Γ ⊩ʳ⟨ l ⟩ z ∷[ mo ] A [ zero ] / [Γ] / [A₀])
         → (⊩ʳs : δ ∙ ⌜ mo ⌝ · p ∙ ⌜ mo ⌝ · r ▸ Γ ∙ ℕ ∙ A ⊩ʳ⟨ l ⟩ s
                  ∷[ mo ] wk1 (A [ (suc (var x0)) ]↑)
                  / [Γ] ∙ [ℕ] ∙ [A] / [A₊])
         → ([m] : ε ⊩⟨ l ⟩ m ∷ ℕ / proj₁ (unwrap [ℕ] ε [σ]))
         → (n®w : m ® w ∷ℕ)
         → natrec p r (subst (liftSubst σ) A) (subst σ z) (subst (liftSubstn σ 2) s) m
           ®⟨ l ⟩ T.natrec (T.subst σ′ (erase z)) (T.subst (T.liftSubstn σ′ 2) (erase s)) w
           ∷ subst (consSubst σ m) A ◂ ⌜ mo ⌝
           / proj₁ (unwrap [A] ε ([σ] , [m]))
natrecʳ″ {mo = 𝟘ᵐ} = _

natrecʳ″
  {n = n} {A = A} {z = z} {s = s} {σ = σ} {σ′ = σ′} {mo = 𝟙ᵐ} {γ = γ}
  {η = η} {δ = δ} {p = p} {r = r} {l = l} {m = m} {w = w} {Γ = Γ}
  [Γ] [A] [A₊] [A₀] [z] [s] [σ] σ®σ′ ⊩ʳz ⊩ʳs [m] (zeroᵣ m⇒zero w⇒zero) =
  let [ℕ] = ℕᵛ {l = l} [Γ]
      [σA₀] = proj₁ (unwrap [A₀] ε [σ])
      [σz] = proj₁ ([z] ε [σ])
      ⊢σz = escapeTerm [σA₀] [σz]
      ⊢σz′ = PE.subst (λ G → ε ⊢ subst σ z ∷ G) (singleSubstLift A zero) ⊢σz
      [σA] = proj₁ (unwrap [A] (ε ∙ ℕⱼ ε) (liftSubstS {F = ℕ} [Γ] ε [ℕ] [σ]))
      ⊢σA = escape [σA]
      [σA[m]] = proj₁ (unwrap [A] {σ = consSubst σ m} ε ([σ] , [m]))
      [⇑²σ] = liftSubstS {F = A} (_∙_ {A = ℕ} [Γ] [ℕ]) (ε ∙ (ℕⱼ ε)) [A]
                                 (liftSubstS {F = ℕ} [Γ] ε [ℕ] [σ])
      [σA₊] = proj₁ (unwrap [A₊] {σ = liftSubstn σ 2} (ε ∙ ℕⱼ ε ∙ ⊢σA) [⇑²σ])
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
      nrw⇒nr0 = TP.natrec-subst* {s = T.subst (T.liftSubst (T.liftSubst σ′)) (erase s)} w⇒zero
      nrw⇒z = TP.red*concat nrw⇒nr0 (T.trans T.natrec-zero T.refl)
      z®z′ = ⊩ʳz [σ] (subsumptionSubst {l = l} σ®σ′
                                       (≤ᶜ-trans (⊛ᶜ-decreasingˡ (γ ∧ᶜ η) (δ +ᶜ p ·ᶜ η) r)
                                                 (∧ᶜ-decreasingˡ γ η)))
      [σA₀]′ = I.irrelevance′ (singleSubstLift A zero) [σA₀]
      z®z″ = irrelevanceTerm′ (singleSubstLift A zero) [σA₀] [σA₀]′ z®z′
      nr®nr = redSubstTerm* [σA₀]′ z®z″ nrm⇒z nrw⇒z
      [σA₀]″ = I.irrelevance′ (singleSubstComp zero σ A) [σA₀]′
      [σA[m]]′ = I.irrelevance′ (PE.sym (singleSubstComp m σ A)) [σA[m]]
      nr®nr′ = convTermʳ _ [σA₀]′ [σA[m]]′ (sym A[m]≡A[0]) nr®nr
  in  irrelevanceTerm′ (singleSubstComp m σ A) [σA[m]]′ [σA[m]] nr®nr′
natrecʳ″
  {n = n} {A = A} {z = z} {s = s} {σ = σ} {σ′ = σ′} {mo = 𝟙ᵐ} {γ = γ}
  {η = η} {δ = δ} {p = p} {r = r} {l = l} {m = m} {w = w} {Γ = Γ}
  [Γ] [A] [A₊] [A₀] [z] [s] [σ] σ®σ′ ⊩ʳz ⊩ʳs [m]
  (sucᵣ {t′ = m′} {v′ = w′} m⇒sucm′ w⇒sucw′ m′®w′) =
  let [ℕ] = ℕᵛ {l = l} [Γ]
      σnrm = natrec p r (subst (liftSubst σ) A) (subst σ z) (subst (liftSubstn σ 2) s) m
      σnrm′ = natrec p r (subst (liftSubst σ) A) (subst σ z) (subst (liftSubstn σ 2) s) m′
      σnrw′ = T.natrec (T.subst σ′ (erase z)) (T.subst (T.liftSubstn σ′ 2) (erase s)) w′
      [σA₀] = proj₁ (unwrap [A₀] ε [σ])
      [σz] = proj₁ ([z] ε [σ])
      ⊢σz = escapeTerm [σA₀] [σz]
      ⊢σz′ = PE.subst (λ G → ε ⊢ subst σ z ∷ G) (singleSubstLift A zero) ⊢σz
      [σA] = proj₁ (unwrap [A] (ε ∙ ℕⱼ ε) (liftSubstS {F = ℕ} [Γ] ε [ℕ] [σ]))
      ⊢σA = escape [σA]
      [σA[m]] = proj₁ (unwrap [A] {σ = consSubst σ m} ε ([σ] , [m]))
      [σA[m]]′ = I.irrelevance′ (PE.sym (singleSubstComp m σ A)) [σA[m]]
      [⇑²σ] = liftSubstS {F = A} (_∙_ {A = ℕ} [Γ] [ℕ]) (ε ∙ (ℕⱼ ε)) [A]
                                 (liftSubstS {F = ℕ} [Γ] ε [ℕ] [σ])
      [σA₊] = proj₁ (unwrap [A₊] {σ = liftSubstn σ 2} (ε ∙ ℕⱼ ε ∙ ⊢σA) [⇑²σ])
      ⊢σA₊ = escape [σA₊]
      [σs] = proj₁ ([s] {σ = liftSubstn σ 2} (ε ∙ ℕⱼ ε ∙ ⊢σA) [⇑²σ])
      ⊢σs = escapeTerm [σA₊] [σs]
      ⊢σs′ = PE.subst (λ G → ε ∙ ℕ ∙ (subst (liftSubst σ) A) ⊢ subst (liftSubstn σ 2) s ∷ G)
                      (natrecSucCase σ A) ⊢σs
      ⊢sucm′ = proj₂ (proj₂ (syntacticRedTerm m⇒sucm′))
      [ℕ]′ , [sucm′]′ = reducibleTerm ⊢sucm′
      [sucm′] = I.irrelevanceTerm [ℕ]′ (proj₁ (unwrap [ℕ] ε [σ])) [sucm′]′
      ⊢m′ = proj₁ (inversion-suc ⊢sucm′)
      [ℕ]′ , [m′]′ = reducibleTerm ⊢m′
      [m′] = I.irrelevanceTerm [ℕ]′ (proj₁ (unwrap [ℕ] ε [σ])) [m′]′
      [A[m′]] = proj₁ (unwrap [A] {σ = consSubst σ m′} ε ([σ] , [m′]))
      [A[sucm′]] = proj₁ (unwrap [A] {σ = consSubst σ (suc m′)} ε ([σ] , [sucm′]))
      [A[sucm′]]′ = I.irrelevance′ (PE.sym (singleSubstComp (suc m′) σ A)) [A[sucm′]]
      ⊢nrm′ = natrecⱼ {p = p} {r = r} ⊢σA ⊢σz′ ⊢σs′ ⊢m′
      [G] , [nrm′]′ = reducibleTerm ⊢nrm′
      [nrm′] = I.irrelevanceTerm′ (singleSubstComp m′ σ A) [G] [A[m′]] [nrm′]′
      [σ₊A₊] = proj₁ (unwrap [A₊] {σ = consSubst (consSubst σ m′) σnrm′} ε (([σ] , [m′]) , [nrm′]))
      A[m]≡A[sucm′] = substTypeEq (refl ⊢σA) (subset*Term m⇒sucm′)
      nrm⇒nrsucm′ = natrec-subst* {p = p} {r = r} m⇒sucm′ ⊢σA ⊢σz′ ⊢σs′
      nrm⇒nrsucm″ = conv* nrm⇒nrsucm′ A[m]≡A[sucm′]
      nrsucm′⇒s = natrec-suc ⊢m′ ⊢σA ⊢σz′ ⊢σs′
      nrm⇒s = nrm⇒nrsucm″ ⇨∷* redMany nrsucm′⇒s
      nrw⇒nrsucw′ = TP.natrec-subst* {z = T.subst σ′ (erase z)}
                                     {s = T.subst (T.liftSubst (T.liftSubst σ′)) (erase s)}
                                     w⇒sucw′
      nrw⇒s = TP.red*concat nrw⇒nrsucw′ (T.trans T.natrec-suc T.refl)
      σ®σ′ₛ = subsumptionSubst {l = l} σ®σ′
                               (≤ᶜ-trans (⊛ᶜ-decreasingʳ (γ ∧ᶜ η) (δ +ᶜ p ·ᶜ η) r)
                                         (+ᶜ-decreasingˡ δ (p ·ᶜ η)))
      nrm′®nrw′ = natrecʳ″ {A = A} {z = z} {s = s}
                           [Γ] [A] [A₊] [A₀] [z] [s] [σ] σ®σ′ ⊩ʳz ⊩ʳs [m′] m′®w′
      s®s′ = ⊩ʳs {σ = consSubst (consSubst σ m′) σnrm′}
                 {σ′ = T.consSubst (T.consSubst σ′ w′) σnrw′}
                 (([σ] , [m′]) , [nrm′])
                 ( ( σ®σ′ₛ
                   , subsumptionTerm {q = p} m′®w′ (least-elem p)
                   )
                 , subsumptionTerm {q = r} nrm′®nrw′ (least-elem r)
                 )
      s®s″ = irrelevanceTerm′ (PE.trans (wk1-tail (A [ suc (var x0) ]↑))
                                        (PE.trans (substCompEq A)
                                        (PE.trans (substVar-to-subst substLem A)
                                                  (PE.sym (substCompEq A)))))
                              [σ₊A₊] [A[sucm′]]′ s®s′
      s®s‴ = PE.subst₂ (λ t v → t ®⟨ l ⟩ v ∷ subst (liftSubst σ) A [ suc m′ ] / [A[sucm′]]′)
                       (PE.trans (substVar-to-subst substLem′ s) (PE.sym (substCompEq s)))
                       (PE.trans (TP.substVar-to-subst substLem″ (erase s))
                                 (PE.sym (TP.substCompEq (erase s))))
                       s®s″
      nrm®nrw = redSubstTerm* [A[sucm′]]′ s®s‴ nrm⇒s nrw⇒s
      nrm®nrw′ = convTermʳ _ [A[sucm′]]′ [σA[m]]′ (sym A[m]≡A[sucm′])
                   nrm®nrw
  in  irrelevanceTerm′ (singleSubstComp m σ A) [σA[m]]′ [σA[m]] nrm®nrw′
  where
  substLem : (x : Fin (1+ n))
           → (consSubst σ m′ ₛ•ₛ consSubst (λ x₁ → wk1 (var x₁)) (suc (var x0))) x
           PE.≡ (sgSubst (suc m′) ₛ•ₛ liftSubst σ) x
  substLem x0 = PE.refl
  substLem (x +1) = PE.sym (PE.trans (wk1-tail (σ x)) (subst-id (σ x)))
  substLem′ : (x : Fin (1+ (1+ n)))
            → consSubst (consSubst σ m′) (natrec p r (subst (liftSubst σ) A) (subst σ z)
                        (subst (liftSubstn σ 2) s) m′) x
            PE.≡ (consSubst (consSubst var m′)
                            (natrec p r (subst (liftSubst σ) A) (subst σ z)
                                        (subst (liftSubstn σ 2) s) m′)
                 ₛ•ₛ liftSubstn σ 2) x
  substLem′ x0 = PE.refl
  substLem′ (x0 +1) = PE.refl
  substLem′ (x +1 +1) = PE.sym (PE.trans (wk1-tail (wk1 (σ x)))
                                         (PE.trans (wk1-tail (σ x)) (subst-id (σ x))))
  substLem″ : (x : Fin (1+ (1+ n)))
            → T.consSubst (T.consSubst σ′ w′) (T.natrec (T.subst σ′ (erase z))
                          (T.subst (T.liftSubstn σ′ 2) (erase s)) w′) x
            PE.≡ (T.consSubst (T.consSubst T.idSubst w′)
                              (T.natrec (T.subst σ′ (erase z))
                                        (T.subst (T.liftSubst (T.liftSubst σ′)) (erase s)) w′)
                 T.ₛ•ₛ T.liftSubst (T.liftSubst σ′)) x
  substLem″ x0 = PE.refl
  substLem″ (x0 +1) = PE.refl
  substLem″ (x +1 +1) = PE.sym (PE.trans (TP.wk1-tail (T.wk1 (σ′ x)))
                                         (PE.trans (TP.wk1-tail (σ′ x)) (TP.subst-id (σ′ x))))


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
         → (⊩ʳz : γ ▸ Γ ⊩ʳ⟨ l ⟩ z ∷[ mo ] A [ zero ] / [Γ] / [A₀])
         → (⊩ʳs : δ ∙ ⌜ mo ⌝ · p ∙ ⌜ mo ⌝ · r ▸ Γ ∙ ℕ ∙ A ⊩ʳ⟨ l ⟩ s
                  ∷[ mo ] wk1 (A [ (suc (var x0)) ]↑)
                  / [Γ] ∙ [ℕ] ∙ [A] / [A₊])
         → (⊩ʳm : η ▸ Γ ⊩ʳ⟨ l ⟩ m ∷[ mo ] ℕ / [Γ] / [ℕ])
         → (γ ∧ᶜ η) ⊛ᶜ (δ +ᶜ p ·ᶜ η) ▷ r ▸ Γ
             ⊩ʳ⟨ l ⟩ natrec p r A z s m ∷[ mo ] A [ m ] / [Γ] / [A[m]]
natrecʳ′ {mo = 𝟘ᵐ} = _

natrecʳ′
  {n = n} {A = A} {m = m} {z = z} {s = s} {γ = γ} {mo = 𝟙ᵐ} {δ = δ}
  {p = p} {r = r} {η = η} {l = l} {Γ = Γ}
  [Γ] [A] [A₊] [A₀] [A[m]] [z] [s] [m] ⊩ʳz ⊩ʳs ⊩ʳm {σ} {σ′} [σ] σ®σ′ =
  let [σm] = proj₁ ([m] ε [σ])
      m®w = ⊩ʳm [σ] (subsumptionSubst {l = l} σ®σ′
                                      (≤ᶜ-trans (⊛ᶜ-decreasingˡ (γ ∧ᶜ η) _ r)
                                                (∧ᶜ-decreasingʳ γ η)))
      nr®nr = natrecʳ″ {A = A} {z = z} {s = s}
                       [Γ] [A] [A₊] [A₀] [z] [s] [σ] σ®σ′ ⊩ʳz ⊩ʳs [σm] m®w
  in  irrelevanceTerm′ (PE.sym (PE.trans (singleSubstLift A m) (singleSubstComp (subst σ m) σ A)))
                       (proj₁ (unwrap [A] ε ([σ] , [σm]))) (proj₁ (unwrap [A[m]] ε [σ])) nr®nr

natrecʳ : ∀ {l} {Γ : Con Term n}
         → ([Γ] : ⊩ᵛ Γ)
           (let [ℕ] = ℕᵛ {l = l} [Γ])
           ([A] : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ [ℕ])
           ([A₊] : Γ ∙ ℕ ∙ A ⊩ᵛ⟨ l ⟩ wk1 (A [ (suc (var x0)) ]↑) / [Γ] ∙ [ℕ] ∙ [A])
           ([A₀] : Γ ⊩ᵛ⟨ l ⟩ A [ zero ] / [Γ])
           ([z] : Γ ⊩ᵛ⟨ l ⟩ z ∷ A [ zero ] / [Γ] / [A₀])
           ([s] : Γ ∙ ℕ ∙ A ⊩ᵛ⟨ l ⟩ s ∷  wk1 (A [ (suc (var x0)) ]↑) / [Γ] ∙ [ℕ] ∙ [A] / [A₊])
           ([m] : Γ ⊩ᵛ⟨ l ⟩ m ∷ ℕ / [Γ] / [ℕ])
         → (⊩ʳz : γ ▸ Γ ⊩ʳ⟨ l ⟩ z ∷[ mo ] A [ zero ] / [Γ] / [A₀])
         → (⊩ʳs : δ ∙ ⌜ mo ⌝ · p ∙ ⌜ mo ⌝ · r ▸ Γ ∙ ℕ ∙ A ⊩ʳ⟨ l ⟩ s
                  ∷[ mo ] wk1 (A [ (suc (var x0)) ]↑)
                  / [Γ] ∙ [ℕ] ∙ [A] / [A₊])
         → (⊩ʳm : η ▸ Γ ⊩ʳ⟨ l ⟩ m ∷[ mo ] ℕ / [Γ] / [ℕ])
         → ∃ λ ([A[m]] : Γ ⊩ᵛ⟨ l ⟩ A [ m ] / [Γ])
         → (γ ∧ᶜ η) ⊛ᶜ (δ +ᶜ p ·ᶜ η) ▷ r ▸ Γ ⊩ʳ⟨ l ⟩ natrec p r A z s m
           ∷[ mo ] A [ m ] / [Γ] / [A[m]]
natrecʳ {A = A} {z = z} {s = s} {m = m}
        [Γ] [A] [A₊] [A₀] [z] [s] [m] ⊩ʳz ⊩ʳs ⊩ʳm =
  let [A[m]] = substS {F = ℕ} {G = A}  [Γ] (ℕᵛ [Γ]) [A] [m]
  in  [A[m]] , natrecʳ′ {A = A} {m = m} {z = z} {s = s}
                        [Γ] [A] [A₊] [A₀] [A[m]] [z] [s] [m] ⊩ʳz ⊩ʳs ⊩ʳm
