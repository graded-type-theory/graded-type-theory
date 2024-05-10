------------------------------------------------------------------------
-- Subsumption properties (changing the quantity or mode of the logical
-- relation is allowed in some cases).
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Erasure.LogicalRelation.Assumptions
open import Graded.Modality

module Graded.Erasure.LogicalRelation.Subsumption
  {a} {M : Set a}
  {𝕄 : Modality M}
  {R : Type-restrictions 𝕄}
  (as : Assumptions R)
  where

open Assumptions as
open Modality 𝕄

open import Definition.Untyped M as U
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Substitution R
import Definition.LogicalRelation.Fundamental R as F
import Definition.LogicalRelation.Irrelevance R as I

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Mode 𝕄

open import Graded.Erasure.Extraction 𝕄
open import Graded.Erasure.LogicalRelation as
open import Graded.Erasure.Target as T hiding (_⇒_; _⇒*_)

open import Tools.Empty
open import Tools.Fin
open import Tools.Level
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Unit

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
    l : TypeLevel
    ⊩Γ : ⊩ᵛ Γ

-- Subsumption of quantified logical relation
-- If t ® v ◂ p then t ® v ◂ q if when p ≡ 𝟘 then q ≡ 𝟘

subsumptionTerm : ∀ {l [A]}
                → t ®⟨ l ⟩ v ∷ A ◂ p / [A]
                → (p PE.≡ 𝟘 → q PE.≡ 𝟘)
                → t ®⟨ l ⟩ v ∷ A ◂ q / [A]
subsumptionTerm {p = p} {q} t®v prop with is-𝟘? q
... | yes PE.refl = _
... | no q≢𝟘 with is-𝟘? p
... | yes PE.refl = ⊥-elim (q≢𝟘 (prop PE.refl))
... | no p≢𝟘 = t®v

-- Translations between quantified and non-quantified
-- logical relation

_◀≢𝟘_ : ∀ {l [A]}
      → t ®⟨ l ⟩ v ∷ A ◂ p / [A]
      → p PE.≢ 𝟘
      → t ®⟨ l ⟩ v ∷ A / [A]
_◀≢𝟘_ {p = p} t®v p≢𝟘 with is-𝟘? p
... | yes p≡𝟘 = ⊥-elim (p≢𝟘 p≡𝟘)
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
... | no 𝟘≢𝟘 = ⊥-elim (𝟘≢𝟘 PE.refl)

-- Subsumption of related substitutions
-- If σ ® σ′ ∷ Γ ◂ γ and whenever γ⟨x⟩ ≡ 𝟘 then δ⟨x⟩≡𝟘
-- then σ ® σ′ ∷ Γ ◂ δ

subsumptionSubst : ∀ {σₜ σᵥ [Γ] [σ]}
                 → σₜ ® σᵥ ∷[ m ] Γ ◂ γ / [Γ] / [σ]
                 → (∀ x → γ ⟨ x ⟩ PE.≡ 𝟘 → δ ⟨ x ⟩ PE.≡ 𝟘)
                 → σₜ ® σᵥ ∷[ m ] Γ ◂ δ / [Γ] / [σ]
subsumptionSubst {Γ = ε} {ε} {ε} {[Γ] = ε} {lift lower} σ®σ′ prop = _
subsumptionSubst {m = 𝟘ᵐ} {Γ = Γ ∙ x} {γ ∙ p} {δ ∙ q}
                 {[Γ] = [Γ] ∙ [A]} {_ , _} (σ®σ′ , t®v) prop with is-𝟘? (𝟘 · q)
... | yes _ = subsumptionSubst σ®σ′ (λ x → prop (x +1)) , _
... | no 𝟘q≢𝟘 = ⊥-elim (𝟘q≢𝟘 (·-zeroˡ q))
subsumptionSubst {m = 𝟙ᵐ} {Γ = Γ ∙ x} {γ ∙ p} {δ ∙ q}
                 {[Γ] = [Γ] ∙ [A]} {_ , _} (σ®σ′ , t®v) prop
  rewrite ·-identityˡ q rewrite ·-identityˡ p with is-𝟘? q
... | yes q≡𝟘 = subsumptionSubst σ®σ′ (λ x → prop (x +1)) , _
... | no q≢𝟘 with is-𝟘? p
... | yes p≡𝟘 = ⊥-elim (q≢𝟘 (prop x0 p≡𝟘))
... | no p≢𝟘 = subsumptionSubst σ®σ′ (λ x → prop (x +1)) , t®v

-- If σₜ ® σᵥ ∷[ m ] Γ ◂ γ / [Γ] / [σ] holds when m is 𝟙ᵐ, then it
-- holds for any mode.

subsumptionSubstMode :
  ∀ {σₜ σᵥ [Γ] [σ]} →
  σₜ ® σᵥ ∷[ 𝟙ᵐ ] Γ ◂ γ / [Γ] / [σ] →
  σₜ ® σᵥ ∷[ m ] Γ ◂ γ / [Γ] / [σ]
subsumptionSubstMode {m = 𝟙ᵐ} ok =
  ok
subsumptionSubstMode {γ = ε} {[Γ] = ε} =
  _
subsumptionSubstMode {γ = _ ∙ p} {m = 𝟘ᵐ} {[Γ] = _ ∙ _} (ok₁ , _)
  rewrite ·-zeroˡ p with is-𝟘? 𝟘
... | yes p≡𝟘 = subsumptionSubstMode ok₁ , lift tt
... | no p≢𝟘 = ⊥-elim (p≢𝟘 PE.refl)


-- Subsumption of erasure validity
-- If δ ▸ Γ ⊩ʳ t ∷ A and whenever γ⟨x⟩≡𝟘 then δ⟨x⟩≡𝟘
-- then γ ▸ Γ ⊩ʳ t ∷ A

subsumption : ∀ {l} {Γ : U.Con U.Term n} {t A : U.Term n}
            → ([Γ] : ⊩ᵛ Γ) ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
            → δ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ] A / [Γ] / [A]
            → (∀ x → γ ⟨ x ⟩ PE.≡ 𝟘 → δ ⟨ x ⟩ PE.≡ 𝟘)
            → γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ] A / [Γ] / [A]
subsumption [Γ] [A] δ⊩ʳt prop [σ] σ®σ′ =
  δ⊩ʳt [σ] (subsumptionSubst σ®σ′ prop)

opaque

  -- A special case of subsumption.

  subsumption-≤ :
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet ⦄ →
    ∀ t (⊩A : Γ ⊩ᵛ⟨ l ⟩ A / ⊩Γ) →
    γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ] A / ⊩Γ / ⊩A →
    δ ≤ᶜ γ →
    δ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ] A / ⊩Γ / ⊩A
  subsumption-≤ t ⊩A γ⊩ʳt δ≤γ =
    subsumption {t = t} _ ⊩A γ⊩ʳt (λ _ → ≤ᶜ→⟨⟩≡𝟘→⟨⟩≡𝟘 δ≤γ)

subsumption′ : ∀ {l} {Γ : U.Con U.Term n} {t A : U.Term n}
             → ([Γ] : ⊩ᵛ Γ) ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
             → (∀ {σ σ′}
                → ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
                → σ ® σ′ ∷[ m ] Γ ◂ γ / [Γ] / [σ]
                → t U.[ σ ] ®⟨ l ⟩ erase str t T.[ σ′ ]
                  ∷ A U.[ σ ] / proj₁ (unwrap [A] ⊢Δ [σ]))
             → γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ] A / [Γ] / [A]
subsumption′ [Γ] [A] ⊩ʳt [σ] σ®σ′ = ⊩ʳt [σ] σ®σ′ ◀ _

-- Under erased contexts, any substitutions are related

erasedSubst : ∀ {σ σ′}
            → ([Γ] : ⊩ᵛ Γ)
            → ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
            → σ ® σ′ ∷[ m ] Γ ◂ 𝟘ᶜ / [Γ] / [σ]
erasedSubst ε (lift tt) = lift tt
erasedSubst {m = m} ([Γ] ∙ [A]) ([σ] , [t])
  rewrite ·-zeroʳ ⌜ m ⌝ with is-𝟘? 𝟘
... | yes p≡𝟘 = erasedSubst [Γ] [σ] , lift tt
... | no p≢𝟘 = ⊥-elim (p≢𝟘 PE.refl)
