open import Definition.Typed.EqualityRelation
import Definition.Typed as T
import Definition.Untyped as U′ using (Con; Term)
open import Definition.Modality
open import Tools.Nullary
import Tools.PropositionalEquality as PE

module Erasure.LogicalRelation.Subsumption
  {a k} {M : Set a} (𝕄 : Modality M)
  (open U′ M) (open T M) (open Modality 𝕄)
  {Δ : Con Term k} (⊢Δ : ⊢ Δ)
  (is-𝟘? : (p : M) → Dec (p PE.≡ 𝟘))
  {{eqrel : EqRelSet M}}
  where

open EqRelSet {{...}}

open import Definition.Untyped M as U
open import Definition.LogicalRelation.Substitution M
import Definition.LogicalRelation.Fundamental M as F
import Definition.LogicalRelation.Irrelevance M as I

open import Definition.Modality.Context 𝕄
open import Definition.Modality.Properties 𝕄
open import Definition.Mode 𝕄

open import Erasure.Extraction 𝕄 is-𝟘?
open import Erasure.LogicalRelation 𝕄 ⊢Δ is-𝟘?
open import Erasure.Target as T hiding (_⇒_; _⇒*_)

open import Tools.Fin
open import Tools.Function
open import Tools.Level
open import Tools.Nat
open import Tools.Nullary
open import Tools.Product
open import Tools.Sum
open import Tools.Unit

-- open Modality ErasureModality using (·-zeroʳ)

private
  variable
    n : Nat
    t t′ A : U.Term n
    v v′ : T.Term n
    Γ : U.Con U.Term n
    F G : U.Term n
    p q : M
    γ δ : Conₘ n
    m m′ : Mode

-- Subsumption of quantified logical relation
-- If t ® v ◂ p then t ® v ◂ q if when p ≡ 𝟘 then q ≡ 𝟘

subsumptionTerm : ∀ {l [A]}
                → t ®⟨ l ⟩ v ∷ A ◂ p / [A]
                → (p PE.≡ 𝟘 → q PE.≡ 𝟘)
                → t ®⟨ l ⟩ v ∷ A ◂ q / [A]
subsumptionTerm {p = p} {q} t®v prop with is-𝟘? q
... | yes PE.refl = _
... | no q≢𝟘 with is-𝟘? p
... | yes PE.refl = PE.⊥-elim (q≢𝟘 (prop PE.refl))
... | no p≢𝟘 = t®v

-- Translations between quantified and non-quantified
-- logical relation

_◀≢𝟘_ : ∀ {l [A]}
      → t ®⟨ l ⟩ v ∷ A ◂ p / [A]
      → p PE.≢ 𝟘
      → t ®⟨ l ⟩ v ∷ A / [A]
_◀≢𝟘_ {p = p} t®v p≢𝟘 with is-𝟘? p
... | yes p≡𝟘 = PE.⊥-elim (p≢𝟘 p≡𝟘)
... | no p≢𝟘 = t®v

_◀_ : ∀ {l [A]}
    → t ®⟨ l ⟩ v ∷ A / [A] → (p : M)
    → t ®⟨ l ⟩ v ∷ A ◂ p / [A]
t®v ◀ p with is-𝟘? p
... | yes p≡𝟘 = _
... | no p≢𝟘 = t®v

-- Any terms are related at quantity zero

t®v◂𝟘 : ∀ {l [A]}
      → t ®⟨ l ⟩ v ∷ A ◂ 𝟘 / [A]
t®v◂𝟘 with is-𝟘? 𝟘
... | yes _ = _
... | no 𝟘≢𝟘 = PE.⊥-elim (𝟘≢𝟘 PE.refl)

-- Subsumption of related substitutions
-- If σ ® σ′ ∷ Γ ◂ γ and γ ≤ᶜ δ then σ ® σ′ ∷ Γ ◂ δ

subsumptionSubst : ∀ {l σₜ σᵥ [Γ] [σ]}
                 → σₜ ®⟨ l ⟩ σᵥ ∷[ m ] Γ ◂ γ / [Γ] / [σ]
                 → (∀ x → γ ⟨ x ⟩ PE.≡ 𝟘 → δ ⟨ x ⟩ PE.≡ 𝟘)
                 → σₜ ®⟨ l ⟩ σᵥ ∷[ m ] Γ ◂ δ / [Γ] / [σ]
subsumptionSubst {Γ = ε} {ε} {ε} {[Γ] = ε} {lift lower} σ®σ′ prop = _
subsumptionSubst {m = 𝟘ᵐ} {Γ = Γ ∙ x} {γ ∙ p} {δ ∙ q} {l = l}
                 {[Γ] = [Γ] ∙ [A]} {_ , _} (σ®σ′ , t®v) prop with is-𝟘? (𝟘 · q)
... | yes _ = subsumptionSubst {l = l} σ®σ′ (λ x → prop (x +1)) , _
... | no 𝟘q≢𝟘 = PE.⊥-elim (𝟘q≢𝟘 (·-zeroˡ q))
subsumptionSubst {m = 𝟙ᵐ} {Γ = Γ ∙ x} {γ ∙ p} {δ ∙ q} {l = l}
                 {[Γ] = [Γ] ∙ [A]} {_ , _} (σ®σ′ , t®v) prop
  rewrite ·-identityˡ q rewrite ·-identityˡ p with is-𝟘? q
... | yes q≡𝟘 = subsumptionSubst {l = l} σ®σ′ (λ x → prop (x +1)) , _
... | no q≢𝟘 with is-𝟘? p
... | yes p≡𝟘 = PE.⊥-elim (q≢𝟘 (prop x0 p≡𝟘))
... | no p≢𝟘 = subsumptionSubst {l = l} σ®σ′ (λ x → prop (x +1)) , t®v

-- If σₜ ®⟨ l ⟩ σᵥ ∷[ m ] Γ ◂ γ / [Γ] / [σ] holds when m is 𝟙ᵐ, then
-- it holds for any mode.

subsumptionSubstMode :
  ∀ {σₜ σᵥ [Γ] [σ]} l →
  σₜ ®⟨ l ⟩ σᵥ ∷[ 𝟙ᵐ ] Γ ◂ γ / [Γ] / [σ] →
  σₜ ®⟨ l ⟩ σᵥ ∷[ m ] Γ ◂ γ / [Γ] / [σ]
subsumptionSubstMode {m = 𝟙ᵐ} _ ok =
  ok
subsumptionSubstMode {γ = ε} {[Γ] = ε} =
  _
subsumptionSubstMode {γ = _ ∙ p} {m = 𝟘ᵐ} {[Γ] = _ ∙ _} l (ok₁ , _)
  rewrite ·-zeroˡ p with is-𝟘? 𝟘
... | yes p≡𝟘 = subsumptionSubstMode l ok₁ , lift tt
... | no p≢𝟘 = PE.⊥-elim (p≢𝟘 PE.refl)


-- Subsumption of erasure validity
-- If γ ▸ Γ ⊩ʳ t ∷ A and δ ≤ᶜ γ then δ ▸ Γ ⊩ʳ t ∷ A

subsumption : ∀ {l} {Γ : U.Con U.Term n} {t A : U.Term n}
            → ([Γ] : ⊩ᵛ Γ) ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
            → γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ] A / [Γ] / [A]
            → (∀ x → δ ⟨ x ⟩ PE.≡ 𝟘 → γ ⟨ x ⟩ PE.≡ 𝟘)
            → δ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ] A / [Γ] / [A]
subsumption {l = l} [Γ] [A] γ⊩ʳt prop [σ] σ®σ′ =
  γ⊩ʳt [σ] (subsumptionSubst {l = l} σ®σ′ prop)

subsumption′ : ∀ {l} {Γ : U.Con U.Term n} {t A : U.Term n}
             → ([Γ] : ⊩ᵛ Γ) ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
             → (∀ {σ σ′}
                → ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
                → σ ®⟨ l ⟩ σ′ ∷[ m ] Γ ◂ γ / [Γ] / [σ]
                → U.subst σ t ®⟨ l ⟩ T.subst σ′ (erase t)
                  ∷ U.subst σ A / proj₁ (unwrap [A] ⊢Δ [σ]))
             → γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ] A / [Γ] / [A]
subsumption′ [Γ] [A] ⊩ʳt [σ] σ®σ′ = ⊩ʳt [σ] σ®σ′ ◀ _

-- Under erased contexts, any substitutions are related

erasedSubst : ∀ {l σ σ′}
            → ([Γ] : ⊩ᵛ Γ)
            → ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
            → σ ®⟨ l ⟩ σ′ ∷[ m ] Γ ◂ 𝟘ᶜ / [Γ] / [σ]
erasedSubst ε (lift tt) = lift tt
erasedSubst {m = m} (_∙_ {l = l} [Γ] [A]) ([σ] , [t])
  rewrite ·-zeroʳ ⌜ m ⌝ with is-𝟘? 𝟘
... | yes p≡𝟘 = erasedSubst {l = l} [Γ] [σ] , lift tt
... | no p≢𝟘 = PE.⊥-elim (p≢𝟘 PE.refl)
