open import Definition.Modality.Instances.Erasure
open import Definition.Modality.Restrictions
open import Definition.Typed.EqualityRelation

module Erasure.LogicalRelation.Subsumption
  (restrictions : Restrictions Erasure)
  {{eqrel : EqRelSet Erasure}}
  where

open EqRelSet {{...}}

open import Definition.Modality.Instances.Erasure.Modality restrictions
open import Definition.LogicalRelation.Substitution Erasure
import Definition.LogicalRelation.Fundamental Erasure as F
import Definition.LogicalRelation.Irrelevance Erasure as I

open import Definition.Modality.Context ErasureModality
open import Definition.Modality.Properties ErasureModality
open import Definition.Mode ErasureModality
open import Definition.Untyped Erasure as U hiding (_∷_)

open import Erasure.LogicalRelation restrictions
open import Erasure.Target as T hiding (_⇒_; _⇒*_)

open import Tools.Level
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Unit

private
  variable
    n : Nat
    t t′ A : U.Term 0
    v v′ : T.Term 0
    Γ : Con U.Term n
    F G : U.Term n
    p q : Erasure
    γ δ : Conₘ n
    m : Mode

-- Subsumption of quantified logical relation
-- If t ® v ◂ p and p ≤ q then t ® v ◂ q

subsumptionTerm : ∀ {l [A]}
                → t ®⟨ l ⟩ v ∷ A ◂ p / [A]
                → p ≤ q
                → t ®⟨ l ⟩ v ∷ A ◂ q / [A]
subsumptionTerm {p = 𝟘} {𝟘} t®v q≤p = t®v
subsumptionTerm {p = ω} {𝟘} t®v q≤p = tt
subsumptionTerm {p = ω} {ω} t®v q≤p = t®v

-- Subsumption of related substitutions
-- If σ ® σ′ ∷ Γ ◂ γ and γ ≤ᶜ δ then σ ® σ′ ∷ Γ ◂ δ

subsumptionSubst : ∀ {l σₜ σᵥ [Γ] [σ]}
                 → σₜ ®⟨ l ⟩ σᵥ ∷[ m ] Γ ◂ γ / [Γ] / [σ]
                 → γ ≤ᶜ δ
                 → σₜ ®⟨ l ⟩ σᵥ ∷[ m ] Γ ◂ δ / [Γ] / [σ]
subsumptionSubst {Γ = ε} {ε} {ε} {[Γ] = ε} {lift tt} tt ε = tt
subsumptionSubst {m = m} {Γ = Γ ∙ x} {γ ∙ p} {δ ∙ q} {l = l}
                 {[Γ] = [Γ] ∙ [A]} {_ , _} (σ®σ′ , t®v) (γ≤δ ∙ p≤q) =
    subsumptionSubst {l = l} σ®σ′ γ≤δ
  , subsumptionTerm t®v (·-monotoneʳ {r = ⌜ m ⌝} p≤q)

-- Subsumption of erasure validity
-- If γ ▸ Γ ⊩ʳ t ∷ A and δ ≤ᶜ γ then δ ▸ Γ ⊩ʳ t ∷ A

subsumption : ∀ {l} {Γ : Con U.Term n} {t A : U.Term n}
            → ([Γ] : ⊩ᵛ Γ) ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
            → γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ] A / [Γ] / [A]
            → δ ≤ᶜ γ
            → δ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ] A / [Γ] / [A]
subsumption {l = l} [Γ] [A] γ⊩ʳt δ≤γ [σ] σ®σ′ =
  γ⊩ʳt [σ] (subsumptionSubst {l = l} σ®σ′ δ≤γ)

-- If erasure is valid for the mode 𝟙ᵐ, then it is valid for any mode.

subsumptionMode :
  ∀ {l} {Γ : Con U.Term n} {[Γ] : ⊩ᵛ Γ}
  (t {A} : U.Term n) ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ]) →
  γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ 𝟙ᵐ ] A / [Γ] / [A] →
  γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ] A / [Γ] / [A]
subsumptionMode {m = 𝟘ᵐ}        = _
subsumptionMode {m = 𝟙ᵐ} _ _ ok = ok
