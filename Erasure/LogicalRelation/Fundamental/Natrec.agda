{-# OPTIONS --without-K  #-}
open import Definition.Modality.Erasure

open import Definition.Typed.EqualityRelation


module Erasure.LogicalRelation.Fundamental.Natrec {{eqrel : EqRelSet Erasure}} where
open EqRelSet {{...}}

open import Definition.Untyped Erasure as U hiding (_∷_)
open import Definition.Untyped.Properties Erasure
open import Definition.Typed Erasure
open import Definition.Typed.Properties Erasure
-- open import Definition.Typed.RedSteps Erasure
-- open import Definition.Typed.Weakening Erasure
open import Definition.Typed.Consequences.Reduction Erasure
open import Definition.Typed.Consequences.Substitution Erasure

open import Definition.LogicalRelation Erasure
import Definition.LogicalRelation.Irrelevance Erasure as I
open import Definition.LogicalRelation.Substitution Erasure
open import Definition.LogicalRelation.Substitution.Properties Erasure
open import Definition.LogicalRelation.Substitution.Introductions.Nat Erasure
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
open import Erasure.Target.Properties.Reduction

open import Tools.Fin
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n
    t z m : Term n
    A : Term (1+ n)
    s : Term (1+ (1+ n))
    v : T.Term n
    p r : Erasure
    γ δ η : Conₘ n
    σ : Subst 0 n
    σ′ : T.Subst 0 n

zeroCaseRed : t ® v ∷ℕ → ε ⊢ t ⇒* zero ∷ ℕ → v T.⇒* T.zero
zeroCaseRed (zeroᵣ x x₁) t⇒zero = x₁
zeroCaseRed (sucᵣ x x₁ t®v) t⇒zero with whrDet*Term (t⇒zero , zeroₙ) (x , sucₙ)
... | ()

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
      ⊩ʳnr = natrecʳ′ [Γ] [ℕ] [A] [A₊] [A₀] {!!} [z] [s] {!!} [σ] σ®σ′ ⊩ʳz ⊩ʳs {!!} {!x!}
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
