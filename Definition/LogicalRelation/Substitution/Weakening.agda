------------------------------------------------------------------------
-- The logical relation is closed under weakenings
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Weakening
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}

open import Definition.Untyped M
open import Definition.Untyped.Properties M
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Substitution R

open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n           : Nat
    Γ           : Con Term n
    A A₁ A₂ B t : Term _
    l l′        : TypeLevel
    ⊩Γ          : ⊩ᵛ _

opaque

  -- Weakening of valid types by one.
  wk1ᵛ : ∀ {A F l}
        ([Γ] : ⊩ᵛ Γ)
        ([F] : Γ ⊩ᵛ⟨ l′ ⟩ F / [Γ])
      → Γ ⊩ᵛ⟨ l ⟩ A / [Γ]
      → Γ ∙ F ⊩ᵛ⟨ l ⟩ wk1 A / [Γ] ∙ [F]
  wk1ᵛ {A = A} [Γ] [F] [A] = wrap λ ⊢Δ [σ] →
    let [σA] = proj₁ (unwrap [A] ⊢Δ (proj₁ [σ]))
        [σA]′ = irrelevance′ (PE.sym (subst-wk A)) [σA]
    in  [σA]′
    ,   (λ [σ′] [σ≡σ′] →
           irrelevanceEq″ (PE.sym (subst-wk A))
                          (PE.sym (subst-wk A))
                          [σA] [σA]′
                          (proj₂ (unwrap [A] ⊢Δ (proj₁ [σ])) (proj₁ [σ′]) (proj₁ [σ≡σ′])))

opaque
  unfolding wk1ᵛ

  -- Weakening of valid type equality by one.
  wk1Eqᵛ : ∀ {A B F l}
           ([Γ] : ⊩ᵛ Γ)
           ([F] : Γ ⊩ᵛ⟨ l′ ⟩ F / [Γ])
           ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
           ([A≡B] : Γ ⊩ᵛ⟨ l ⟩ A ≡ B / [Γ] / [A])
         → Γ ∙ F ⊩ᵛ⟨ l ⟩ wk1 A ≡ wk1 B / [Γ] ∙ [F] / wk1ᵛ {A = A} {F} [Γ] [F] [A]
  wk1Eqᵛ {A = A} {B} [Γ] [F] [A] [A≡B] ⊢Δ [σ] =
    let [σA] = proj₁ (unwrap [A] ⊢Δ (proj₁ [σ]))
        [σA]′ = irrelevance′ (PE.sym (subst-wk A)) [σA]
    in  irrelevanceEq″ (PE.sym (subst-wk A))
                       (PE.sym (subst-wk B))
                       [σA] [σA]′
                       ([A≡B] ⊢Δ (proj₁ [σ]))

opaque

  -- Weakening of valid terms by one.

  wk1Termᵛ :
    ∀ t →
    (⊩A : Γ ⊩ᵛ⟨ l ⟩ A / ⊩Γ)
    (⊩B : Γ ⊩ᵛ⟨ l′ ⟩ B / ⊩Γ) →
    Γ ⊩ᵛ⟨ l ⟩ t ∷ A / ⊩Γ / ⊩A →
    Γ ∙ B ⊩ᵛ⟨ l ⟩ wk1 t ∷ wk1 A / ⊩Γ ∙ ⊩B / wk1ᵛ ⊩Γ ⊩B ⊩A
  wk1Termᵛ {A} t ⊩A ⊩B ⊩t _ ⊩σ,@(⊩σ , _) =
    let ⊩A[σ]      , _ = ⊩A .unwrap _ ⊩σ
        ⊩wk1-A[σ,] , _ = wk1ᵛ _ ⊩B ⊩A .unwrap _ ⊩σ,
    in
      irrelevanceTerm″
        (PE.sym (subst-wk A))
        (PE.sym (subst-wk t))
        ⊩A[σ]
        ⊩wk1-A[σ,]
        (⊩t _ ⊩σ .proj₁)
    , λ (⊩σ′ , _) (⊩σ≡σ′ , _) →
        irrelevanceEqTerm″
          (PE.sym (subst-wk t))
          (PE.sym (subst-wk t))
          (PE.sym (subst-wk A))
          ⊩A[σ]
          ⊩wk1-A[σ,]
          (⊩t _ _ .proj₂ ⊩σ′ ⊩σ≡σ′)

opaque

  -- A variant of wk1Termᵛ for equality.

  wk1EqTermᵛ :
    {⊩A₁ : Γ ⊩ᵛ⟨ l ⟩ A₁ / ⊩Γ}
    {⊩B : Γ ⊩ᵛ⟨ l′ ⟩ B / ⊩Γ} →
    ∀ t₁ t₂ →
    Γ ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ A₁ / ⊩Γ / ⊩A₁ →
    Γ ∙ B ⊩ᵛ⟨ l ⟩ wk1 t₁ ≡ wk1 t₂ ∷ wk1 A₁ / ⊩Γ ∙ ⊩B / wk1ᵛ ⊩Γ ⊩B ⊩A₁
  wk1EqTermᵛ {A₁} {⊩A₁} t₁ t₂ ⊩t₁≡t₂ _ ⊩σ,@(⊩σ , _) =
    irrelevanceEqTerm″
      (PE.sym (subst-wk t₁))
      (PE.sym (subst-wk t₂))
      (PE.sym (subst-wk A₁))
      (⊩A₁ .unwrap _ ⊩σ .proj₁)
      (wk1ᵛ _ _ ⊩A₁ .unwrap _ ⊩σ, .proj₁)
      (⊩t₁≡t₂ _ ⊩σ)
