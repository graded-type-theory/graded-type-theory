------------------------------------------------------------------------
-- Graded.Erasure validity of natrec.
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

open import Definition.Typed.Restrictions
open import Graded.Erasure.LogicalRelation.Assumptions
open import Graded.Modality

module Graded.Erasure.LogicalRelation.Fundamental.Natrec
  {a} {M : Set a}
  {𝕄 : Modality M}
  (open Modality 𝕄)
  {R : Type-restrictions 𝕄}
  (as : Assumptions R)
  ⦃ 𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet ⦄
  where

open Assumptions as

open import Definition.Untyped M hiding (_∷_)
open import Definition.Untyped.Properties M
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.RedSteps R
open import Definition.Typed.Consequences.RedSteps R
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Consequences.Reduction R
open import Definition.Typed.Consequences.Substitution R
open import Definition.Typed.Consequences.Syntactic R

open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Fundamental.Reducibility R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.Properties R
open import Definition.LogicalRelation.Substitution.Introductions.Nat R
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst R
open import Definition.LogicalRelation.Properties.Escape R

import Definition.LogicalRelation.Irrelevance R as I

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Modality.Properties 𝕄
open import Graded.Mode 𝕄

open import Graded.Erasure.LogicalRelation is-𝟘? as
open import Graded.Erasure.LogicalRelation.Conversion is-𝟘? as
open import Graded.Erasure.LogicalRelation.Irrelevance is-𝟘? as
open import Graded.Erasure.LogicalRelation.Subsumption is-𝟘? as
open import Graded.Erasure.LogicalRelation.Reduction is-𝟘? as
open import Graded.Erasure.Extraction 𝕄 is-𝟘?
import Graded.Erasure.Target as T
import Graded.Erasure.Target.Properties as TP

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat hiding (_+_)
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
open import Tools.Relation

private
  variable
    n : Nat
    Γ : Con Term n
    t z m : Term n
    A : Term (1+ n)
    s : Term (2+ n)
    v w : T.Term n
    p q r : M
    γ δ η χ : Conₘ n
    σ : Subst k n
    σ′ : T.Subst k n
    mo : Mode

natrecʳ″ : ∀ {l m w} {Γ : Con Term n}
         → ([Γ] : ⊩ᵛ Γ)
           (let [ℕ] = ℕᵛ {l = l} [Γ])
           ([A] : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ [ℕ])
           ([A₊] : Γ ∙ ℕ ∙ A ⊩ᵛ⟨ l ⟩ A [ (suc (var x1)) ]↑² / [Γ] ∙ [ℕ] ∙ [A])
           ([A₀] : Γ ⊩ᵛ⟨ l ⟩ A [ zero ]₀ / [Γ])
           ([z] : Γ ⊩ᵛ⟨ l ⟩ z ∷ A [ zero ]₀ / [Γ] / [A₀])
           ([s] : Γ ∙ ℕ ∙ A ⊩ᵛ⟨ l ⟩ s ∷  A [ (suc (var x1)) ]↑² / [Γ] ∙ [ℕ] ∙ [A] / [A₊])
           ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
         → (σ®σ′ : σ ® σ′ ∷[ mo ] Γ ◂ χ / [Γ] / [σ])
         → (⊩ʳz : γ ▸ Γ ⊩ʳ⟨ l ⟩ z ∷[ mo ] A [ zero ]₀ / [Γ] / [A₀])
         → (⊩ʳs : δ ∙ ⌜ mo ⌝ · p ∙ ⌜ mo ⌝ · r ▸ Γ ∙ ℕ ∙ A ⊩ʳ⟨ l ⟩ s
                  ∷[ mo ] A [ (suc (var x1)) ]↑²
                  / [Γ] ∙ [ℕ] ∙ [A] / [A₊])
         → (∀ x → χ ⟨ x ⟩ PE.≡ 𝟘 → γ ⟨ x ⟩ PE.≡ 𝟘 × δ ⟨ x ⟩ PE.≡ 𝟘)
         → ([m] : Δ ⊩⟨ l ⟩ m ∷ ℕ / proj₁ (unwrap [ℕ] ⊢Δ [σ]))
         → (n®w : m ® w ∷ℕ)
         → natrec p q r (A [ liftSubst σ ]) (z [ σ ])
             (s [ liftSubstn σ 2 ]) m ®⟨ l ⟩
           T.natrec (erase str z T.[ σ′ ])
             (erase str s T.[ T.liftSubstn σ′ 2 ]) w ∷
           A [ consSubst σ m ] ◂ ⌜ mo ⌝ /
           proj₁ (unwrap [A] ⊢Δ ([σ] , [m]))
natrecʳ″ {mo = 𝟘ᵐ} with is-𝟘? 𝟘
... | yes _ = _
... | no 𝟘≢𝟘 = ⊥-elim (𝟘≢𝟘 PE.refl)

natrecʳ″
  {n = n} {A = A} {z = z} {s = s} {σ = σ} {σ′ = σ′} {mo = 𝟙ᵐ} {γ = γ}
  {p = p} {r = r} {l = l} {m = m} {w = w} {Γ = Γ}
  [Γ] [A] [A₊] [A₀] [z] [s] [σ] σ®σ′ ⊩ʳz ⊩ʳs ≡𝟘→≡𝟘 [m]
  (zeroᵣ m⇒zero w⇒zero)
  with is-𝟘? 𝟙
... | yes 𝟙≡𝟘 = _
... | no 𝟙≢𝟘 =
  let [ℕ] = ℕᵛ {l = l} [Γ]
      [σA₀] = proj₁ (unwrap [A₀] ⊢Δ [σ])
      [σz] = proj₁ ([z] ⊢Δ [σ])
      ⊢σz = escapeTerm [σA₀] [σz]
      ⊢σz′ = PE.subst (λ G → Δ ⊢ z [ σ ] ∷ G) (singleSubstLift A zero) ⊢σz
      [σA] = proj₁ (unwrap [A] (⊢Δ ∙ ℕⱼ ⊢Δ) (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ]))
      ⊢σA = escape [σA]
      [σA[m]] = proj₁ (unwrap [A] {σ = consSubst σ m} ⊢Δ ([σ] , [m]))
      [⇑²σ] = liftSubstS {F = A} (_∙_ {A = ℕ} [Γ] [ℕ]) (⊢Δ ∙ (ℕⱼ ⊢Δ)) [A]
                                 (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ])
      [σA₊] = proj₁ (unwrap [A₊] {σ = liftSubstn σ 2} (⊢Δ ∙ ℕⱼ ⊢Δ ∙ ⊢σA) [⇑²σ])
      ⊢σA₊ = escape [σA₊]
      [σs] = proj₁ ([s] {σ = liftSubstn σ 2} (⊢Δ ∙ ℕⱼ ⊢Δ ∙ ⊢σA) [⇑²σ])
      ⊢σs = escapeTerm [σA₊] [σs]
      ⊢σs′ = PE.subst (λ G → Δ ∙ ℕ ∙ A [ liftSubst σ ] ⊢ s [ liftSubstn σ 2 ] ∷ G)
                      (natrecSucCase σ A) ⊢σs
      A[m]≡A[0] = substTypeEq (refl ⊢σA) (subset*Term m⇒zero)
      nrm⇒nr0 = natrec-subst* {p = p} {r = r} m⇒zero ⊢σA ⊢σz′ ⊢σs′
      nrm⇒nr0′ = conv* nrm⇒nr0 A[m]≡A[0]
      nr0⇒z = natrec-zero ⊢σA ⊢σz′ ⊢σs′
      nrm⇒z = nrm⇒nr0′ ⇨∷* redMany nr0⇒z
      nrw⇒nr0 = TP.natrec-subst* w⇒zero
      nrw⇒z = TP.red*concat nrw⇒nr0 (T.trans T.natrec-zero T.refl)
      z®z′ = ⊩ʳz [σ] $
             subsumptionSubst σ®σ′ (λ _ → proj₁ ∘→ ≡𝟘→≡𝟘 _)
      [σA₀]′ = I.irrelevance′ (singleSubstLift A zero) [σA₀]
      z®z″ = irrelevanceTerm′ (singleSubstLift A zero) [σA₀] [σA₀]′ z®z′
      nr®nr = redSubstTerm* [σA₀]′ z®z″ nrm⇒z nrw⇒z
      [σA₀]″ = I.irrelevance′ (singleSubstComp zero σ A) [σA₀]′
      [σA[m]]′ = I.irrelevance′ (PE.sym (singleSubstComp m σ A)) [σA[m]]
      nr®nr′ = convTermʳ [σA₀]′ [σA[m]]′ (sym A[m]≡A[0]) nr®nr
  in  irrelevanceTerm′ (singleSubstComp m σ A) [σA[m]]′ [σA[m]] nr®nr′
natrecʳ″
  {n = n} {A = A} {z = z} {s = s} {σ = σ} {σ′ = σ′} {mo = 𝟙ᵐ} {γ = γ}
  {p = p} {r = r} {q = q} {l = l} {m = m} {w = w}
  {Γ = Γ}
  [Γ] [A] [A₊] [A₀] [z] [s] [σ] σ®σ′ ⊩ʳz ⊩ʳs ≡𝟘→≡𝟘 [m]
  (sucᵣ {t′ = m′} {v′ = w′} m⇒sucm′ w⇒sucw′ m′®w′)
  with is-𝟘? 𝟙
... | yes 𝟘≡𝟙 = _
... | no 𝟘≢𝟙 =
  let [ℕ] = ℕᵛ {l = l} [Γ]
      σnrm = natrec p q r (A [ liftSubst σ ]) (z [ σ ]) (s [ liftSubstn σ 2 ]) m
      σnrm′ = natrec p q r (A [ liftSubst σ ]) (z [ σ ]) (s [ liftSubstn σ 2 ]) m′
      σnrw′ = T.natrec (erase str z T.[ σ′ ])
                (erase str s T.[ T.liftSubstn σ′ 2 ]) w′
      [σA₀] = proj₁ (unwrap [A₀] ⊢Δ [σ])
      [σz] = proj₁ ([z] ⊢Δ [σ])
      ⊢σz = escapeTerm [σA₀] [σz]
      ⊢σz′ = PE.subst (λ G → Δ ⊢ z [ σ ] ∷ G) (singleSubstLift A zero) ⊢σz
      [σA] = proj₁ (unwrap [A] (⊢Δ ∙ ℕⱼ ⊢Δ) (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ]))
      ⊢σA = escape [σA]
      [σA[m]] = proj₁ (unwrap [A] {σ = consSubst σ m} ⊢Δ ([σ] , [m]))
      [σA[m]]′ = I.irrelevance′ (PE.sym (singleSubstComp m σ A)) [σA[m]]
      [⇑²σ] = liftSubstS {F = A} (_∙_ {A = ℕ} [Γ] [ℕ]) (⊢Δ ∙ (ℕⱼ ⊢Δ)) [A]
                                 (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ])
      [σA₊] = proj₁ (unwrap [A₊] {σ = liftSubstn σ 2} (⊢Δ ∙ ℕⱼ ⊢Δ ∙ ⊢σA) [⇑²σ])
      ⊢σA₊ = escape [σA₊]
      [σs] = proj₁ ([s] {σ = liftSubstn σ 2} (⊢Δ ∙ ℕⱼ ⊢Δ ∙ ⊢σA) [⇑²σ])
      ⊢σs = escapeTerm [σA₊] [σs]
      ⊢σs′ = PE.subst (λ G → Δ ∙ ℕ ∙ A [ liftSubst σ ] ⊢ s [ liftSubstn σ 2 ] ∷ G)
                      (natrecSucCase σ A) ⊢σs
      ⊢sucm′ = proj₂ (proj₂ (syntacticRedTerm m⇒sucm′))
      [ℕ]′ , [sucm′]′ = reducibleTerm ⊢sucm′
      [sucm′] = I.irrelevanceTerm [ℕ]′ (proj₁ (unwrap [ℕ] ⊢Δ [σ])) [sucm′]′
      ⊢m′ = proj₁ (inversion-suc ⊢sucm′)
      [ℕ]′ , [m′]′ = reducibleTerm ⊢m′
      [m′] = I.irrelevanceTerm [ℕ]′ (proj₁ (unwrap [ℕ] ⊢Δ [σ])) [m′]′
      [A[m′]] = proj₁ (unwrap [A] {σ = consSubst σ m′} ⊢Δ ([σ] , [m′]))
      [A[sucm′]] = proj₁ (unwrap [A] {σ = consSubst σ (suc m′)} ⊢Δ ([σ] , [sucm′]))
      [A[sucm′]]′ = I.irrelevance′ (PE.sym (singleSubstComp (suc m′) σ A)) [A[sucm′]]
      ⊢nrm′ = natrecⱼ {p = p} {r = r} ⊢σA ⊢σz′ ⊢σs′ ⊢m′
      [G] , [nrm′]′ = reducibleTerm ⊢nrm′
      [nrm′] = I.irrelevanceTerm′ (singleSubstComp m′ σ A) [G] [A[m′]] [nrm′]′
      [σ₊A₊] = proj₁ (unwrap [A₊] {σ = consSubst (consSubst σ m′) σnrm′} ⊢Δ (([σ] , [m′]) , [nrm′]))
      A[m]≡A[sucm′] = substTypeEq (refl ⊢σA) (subset*Term m⇒sucm′)
      nrm⇒nrsucm′ = natrec-subst* {p = p} {r = r} m⇒sucm′ ⊢σA ⊢σz′ ⊢σs′
      nrm⇒nrsucm″ = conv* nrm⇒nrsucm′ A[m]≡A[sucm′]
      nrsucm′⇒s = natrec-suc ⊢σA ⊢σz′ ⊢σs′ ⊢m′
      nrm⇒s = nrm⇒nrsucm″ ⇨∷* redMany nrsucm′⇒s
      nrw⇒nrsucw′ = TP.natrec-subst* w⇒sucw′
      nrw⇒s = TP.red*concat nrw⇒nrsucw′ (T.trans T.natrec-suc T.refl)
      σ®σ′ₛ = subsumptionSubst σ®σ′ (λ _ → proj₂ ∘→ ≡𝟘→≡𝟘 _)
      nrm′®nrw′ = natrecʳ″ {A = A} {z = z} {s = s}
                           [Γ] [A] [A₊] [A₀] [z] [s] [σ] σ®σ′
                           (subsumption′ {t = z} [Γ] [A₀] ⊩ʳz)
                           (subsumption′ {t = s} ([Γ] ∙ [ℕ] ∙ [A]) [A₊] ⊩ʳs)
                           ≡𝟘→≡𝟘 [m′] m′®w′
      s®s′ = ⊩ʳs {σ = consSubst (consSubst σ m′) σnrm′}
                 {σ′ = T.consSubst (T.consSubst σ′ w′) σnrw′}
                 (([σ] , [m′]) , [nrm′])
                 ( ( σ®σ′ₛ , m′®w′ ◀ _)
                 , subsumptionTerm nrm′®nrw′
                     (λ 1≡𝟘 → ⊥-elim (non-trivial 1≡𝟘))
                 )
      s®s″ = irrelevanceTerm′ (PE.trans (substCompEq A)
                              (PE.trans (substVar-to-subst substLem A) (PE.sym (substCompEq A))))
                              [σ₊A₊] [A[sucm′]]′ s®s′
      s®s‴ = PE.subst₂ (λ t v → t ®⟨ l ⟩ v ∷ A [ liftSubst σ ] [ suc m′ ]₀ / [A[sucm′]]′)
               (PE.trans (substVar-to-subst substLem′ s) $
                PE.sym (substCompEq s))
               (PE.trans
                  (TP.substVar-to-subst substLem″ (erase str s)) $
                PE.sym (TP.substCompEq (erase str s)))
               s®s″
      nrm®nrw = redSubstTerm* [A[sucm′]]′ s®s‴ nrm⇒s nrw⇒s
      nrm®nrw′ = convTermʳ [A[sucm′]]′ [σA[m]]′ (sym A[m]≡A[sucm′])
                   nrm®nrw
  in  irrelevanceTerm′ (singleSubstComp m σ A) [σA[m]]′ [σA[m]] nrm®nrw′
  where
  σnr = natrec p q r (A [ liftSubst σ ]) (z [ σ ])
               (s [ liftSubstn σ 2 ]) m′
  substLem : (x : Fin (1+ n))
           → (consSubst (consSubst σ m′) σnr ₛ•ₛ consSubst (λ z → var (z +2)) (suc (var x1))) x
           PE.≡ (sgSubst (suc m′) ₛ•ₛ liftSubst σ) x
  substLem x0 = PE.refl
  substLem (x +1) = PE.sym (PE.trans (wk1-tail (σ x)) (subst-id (σ x)))

  substLem′ : (x : Fin (2+ n))
            → consSubst (consSubst σ m′) σnr x
            PE.≡ (consSubst (sgSubst m′) σnr ₛ•ₛ liftSubstn σ 2) x
  substLem′ x0 = PE.refl
  substLem′ (x0 +1) = PE.refl
  substLem′ (x +2) = PE.sym (PE.trans (wk1-tail (wk1 (σ x)))
                                         (PE.trans (wk1-tail (σ x)) (subst-id (σ x))))
  substLem″ :
    (x : Fin (2+ n)) →
    T.consSubst (T.consSubst σ′ w′)
      (T.natrec (erase str z T.[ σ′ ])
         (erase str s T.[ T.liftSubstn σ′ 2 ]) w′) x PE.≡
    (T.consSubst (T.consSubst T.idSubst w′)
       (T.natrec (erase str z T.[ σ′ ])
          (erase str s T.[ T.liftSubstn σ′ 2 ]) w′) T.ₛ•ₛ
     T.liftSubst (T.liftSubst σ′)) x
  substLem″ x0 = PE.refl
  substLem″ (x0 +1) = PE.refl
  substLem″ (x +2) = PE.sym (PE.trans (TP.wk1-tail (T.wk1 (σ′ x)))
                                         (PE.trans (TP.wk1-tail (σ′ x)) (TP.subst-id (σ′ x))))


natrecʳ′ : ∀ {l} {Γ : Con Term n}
         → ([Γ] : ⊩ᵛ Γ)
           (let [ℕ] = ℕᵛ {l = l} [Γ])
           ([A] : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ [ℕ])
           ([A₊] : Γ ∙ ℕ ∙ A ⊩ᵛ⟨ l ⟩ A [ (suc (var x1)) ]↑² / [Γ] ∙ [ℕ] ∙ [A])
           ([A₀] : Γ ⊩ᵛ⟨ l ⟩ A [ zero ]₀ / [Γ])
           ([A[m]] : Γ ⊩ᵛ⟨ l ⟩ A [ m ]₀ / [Γ])
           ([z] : Γ ⊩ᵛ⟨ l ⟩ z ∷ A [ zero ]₀ / [Γ] / [A₀])
           ([s] : Γ ∙ ℕ ∙ A ⊩ᵛ⟨ l ⟩ s ∷  A [ (suc (var x1)) ]↑² / [Γ] ∙ [ℕ] ∙ [A] / [A₊])
           ([m] : Γ ⊩ᵛ⟨ l ⟩ m ∷ ℕ / [Γ] / [ℕ])
         → (⊩ʳz : γ ▸ Γ ⊩ʳ⟨ l ⟩ z ∷[ mo ] A [ zero ]₀ / [Γ] / [A₀])
         → (⊩ʳs : δ ∙ ⌜ mo ⌝ · p ∙ ⌜ mo ⌝ · r ▸ Γ ∙ ℕ ∙ A ⊩ʳ⟨ l ⟩ s
                  ∷[ mo ] A [ (suc (var x1)) ]↑²
                  / [Γ] ∙ [ℕ] ∙ [A] / [A₊])
         → (⊩ʳm : η ▸ Γ ⊩ʳ⟨ l ⟩ m ∷[ mo ] ℕ / [Γ] / [ℕ])
         → (∀ x →
            χ ⟨ x ⟩ PE.≡ 𝟘 →
            γ ⟨ x ⟩ PE.≡ 𝟘 × η ⟨ x ⟩ PE.≡ 𝟘 × δ ⟨ x ⟩ PE.≡ 𝟘)
         → χ ▸ Γ ⊩ʳ⟨ l ⟩ natrec p q r A z s m ∷[ mo ] A [ m ]₀ /
             [Γ] / [A[m]]
natrecʳ′ {mo = 𝟘ᵐ} with is-𝟘? 𝟘
... | yes _ = _
... | no 𝟘≢𝟘 = ⊥-elim (𝟘≢𝟘 PE.refl)

natrecʳ′
  {n} {A} {m} {z} {s} {γ} {mo = 𝟙ᵐ} {δ} {p} {r} {η} {Γ}
  [Γ] [A] [A₊] [A₀] [A[m]] [z] [s] [m] ⊩ʳz ⊩ʳs ⊩ʳm ≡𝟘→≡𝟘
  {σ} {σ′} [σ] σ®σ′
  with is-𝟘? 𝟙
... | yes 𝟙≡𝟘 = _
... | no 𝟙≢𝟘 =
  let [σm] = proj₁ ([m] ⊢Δ [σ])
      m®w = ⊩ʳm [σ] $
            subsumptionSubst σ®σ′
              (λ _ → proj₁ ∘→ proj₂ ∘→ ≡𝟘→≡𝟘 _)
      nr®nr = natrecʳ″ {A = A} {z = z} {s = s}
                       [Γ] [A] [A₊] [A₀] [z] [s] [σ] σ®σ′
                       (subsumption′ {t = z} [Γ] [A₀] ⊩ʳz)
                       (subsumption′ {t = s} ([Γ] ∙ _ ∙ [A]) [A₊] ⊩ʳs)
                       (λ _ → Σ.map idᶠ proj₂ ∘→ ≡𝟘→≡𝟘 _) [σm] m®w
  in  irrelevanceTerm′ (PE.sym (PE.trans (singleSubstLift A m) (singleSubstComp (m [ σ ]) σ A)))
                       (proj₁ (unwrap [A] ⊢Δ ([σ] , [σm]))) (proj₁ (unwrap [A[m]] ⊢Δ [σ]))
                       (nr®nr ◀≢𝟘 𝟙≢𝟘)

natrecʳ : ∀ {l} {Γ : Con Term n}
         → ([Γ] : ⊩ᵛ Γ)
           (let [ℕ] = ℕᵛ {l = l} [Γ])
           ([A] : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ [ℕ])
           ([A₊] : Γ ∙ ℕ ∙ A ⊩ᵛ⟨ l ⟩ A [ (suc (var x1)) ]↑² / [Γ] ∙ [ℕ] ∙ [A])
           ([A₀] : Γ ⊩ᵛ⟨ l ⟩ A [ zero ]₀ / [Γ])
           ([z] : Γ ⊩ᵛ⟨ l ⟩ z ∷ A [ zero ]₀ / [Γ] / [A₀])
           ([s] : Γ ∙ ℕ ∙ A ⊩ᵛ⟨ l ⟩ s ∷  A [ (suc (var x1)) ]↑² / [Γ] ∙ [ℕ] ∙ [A] / [A₊])
           ([m] : Γ ⊩ᵛ⟨ l ⟩ m ∷ ℕ / [Γ] / [ℕ])
         → (⊩ʳz : γ ▸ Γ ⊩ʳ⟨ l ⟩ z ∷[ mo ] A [ zero ]₀ / [Γ] / [A₀])
         → (⊩ʳs : δ ∙ ⌜ mo ⌝ · p ∙ ⌜ mo ⌝ · r ▸ Γ ∙ ℕ ∙ A ⊩ʳ⟨ l ⟩ s
                  ∷[ mo ] A [ suc (var x1) ]↑²
                  / [Γ] ∙ [ℕ] ∙ [A] / [A₊])
         → (⊩ʳm : η ▸ Γ ⊩ʳ⟨ l ⟩ m ∷[ mo ] ℕ / [Γ] / [ℕ])
         → (∀ x →
            χ ⟨ x ⟩ PE.≡ 𝟘 →
            γ ⟨ x ⟩ PE.≡ 𝟘 × η ⟨ x ⟩ PE.≡ 𝟘 × δ ⟨ x ⟩ PE.≡ 𝟘)
         → ∃ λ ([A[m]] : Γ ⊩ᵛ⟨ l ⟩ A [ m ]₀ / [Γ])
         → χ ▸ Γ ⊩ʳ⟨ l ⟩ natrec p q r A z s m ∷[ mo ] A [ m ]₀ /
             [Γ] / [A[m]]
natrecʳ {A = A} {z = z} {s = s} {m = m}
        [Γ] [A] [A₊] [A₀] [z] [s] [m] ⊩ʳz ⊩ʳs ⊩ʳm ≡𝟘→≡𝟘 =
  let [A[m]] = substS {F = ℕ} {G = A}  [Γ] (ℕᵛ [Γ]) [A] [m]
  in  [A[m]] ,
      natrecʳ′ {A = A} {m = m} {z = z} {s = s}
        [Γ] [A] [A₊] [A₀] [A[m]] [z] [s] [m] ⊩ʳz ⊩ʳs ⊩ʳm ≡𝟘→≡𝟘
