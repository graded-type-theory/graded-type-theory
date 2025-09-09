------------------------------------------------------------------------
-- Validity of emptyrec.
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Introductions.Emptyrec
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.Untyped M as U hiding (wk)
open import Definition.Untyped.Neutral M type-variant
import Definition.Typed.Weakening R as T
open import Definition.Typed.Properties R
open import Definition.Typed.Reasoning.Reduction R
open import Definition.Typed.Weakening.Definition R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Hidden R
import Definition.LogicalRelation.Hidden.Restricted R as R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.Introductions.Empty R

open import Tools.Function
open import Tools.Product


import Tools.PropositionalEquality as PE

private
  variable
    ∇ : DCon (Term 0) _
    Δ Η : Con Term _
    Γ : Cons _ _
    A A₁ A₂ t t₁ t₂ : Term _
    l l′ : Universe-level
    σ σ₁ σ₂ : Subst _ _
    p : M


------------------------------------------------------------------------
-- The eliminator emptyrec

opaque

  -- Reducibility of equality between applications of emptyrec.

  ⊩emptyrec≡emptyrec :
    ∇ » Δ ⊩ᵛ⟨ l ⟩ A₁ ≡ A₂ →
    ∇ » Δ ⊩ᵛ⟨ l′ ⟩ t₁ ≡ t₂ ∷ Empty →
    ⦃ inc : Var-included or-empty Η ⦄ →
    ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
    ∇ » Η ⊩⟨ l ⟩ emptyrec p A₁ t₁ [ σ₁ ] ≡ emptyrec p A₂ t₂ [ σ₂ ] ∷ A₁ [ σ₁ ]
  ⊩emptyrec≡emptyrec
    {A₁} {A₂} {t₁} {t₂} {σ₁} {σ₂} {p} A₁≡A₂ t₁≡t₂ σ₁≡σ₂ =
    case ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] A₁≡A₂ of λ
      A₁≡A₂ →
    case ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ t₁≡t₂ of λ
      t₁≡t₂ →
    case ⊩≡∷Empty⇔ .proj₁ $ R.⊩≡∷→ $ t₁≡t₂ σ₁≡σ₂ of λ
      (Emptyₜ₌ t₁′ t₂′ t₁[σ₁]⇒*t₁′ t₂[σ₂]⇒*t₂′ _ rest)  →
    case A₁≡A₂ σ₁≡σ₂ of λ
      A₁[σ₁]≡A₂[σ₂] →
    case R.escape-⊩≡ A₁[σ₁]≡A₂[σ₂] of λ
      ⊢A₁[σ₁]≡A₂[σ₂] →
    case R.wf-⊩≡ A₁[σ₁]≡A₂[σ₂] of λ
      (⊩A₁[σ₁] , ⊩A₂[σ₂]) →
    case R.escape-⊩ ⊩A₁[σ₁] of λ
      ⊢A₁[σ₁] →
    case R.escape-⊩ ⊩A₂[σ₂] of λ
      ⊢A₂[σ₂] →
    case rest of λ where
      (ne (neNfₜ₌ t₁′-ne t₂′-ne t₁′~t₂′)) →
        emptyrec p (A₁ [ σ₁ ]) (t₁ [ σ₁ ]) ∷ A₁ [ σ₁ ] ⇒*⟨ emptyrec-subst* t₁[σ₁]⇒*t₁′ ⊢A₁[σ₁] ⟩⊩∷∷
        emptyrec p (A₁ [ σ₁ ]) t₁′         ∷ A₁ [ σ₁ ] ≡⟨ neutral-⊩≡∷ (R.⊩→ ⊩A₁[σ₁])
                                                             (emptyrecₙ t₁′-ne) (emptyrecₙ t₂′-ne)
                                                             (~-emptyrec ⊢A₁[σ₁]≡A₂[σ₂] t₁′~t₂′) ⟩⊩∷∷⇐*
                                                         ⟨ ≅-eq ⊢A₁[σ₁]≡A₂[σ₂] ⟩⇒
        emptyrec p (A₂ [ σ₂ ]) t₂′         ∷ A₂ [ σ₂ ] ⇐*⟨ emptyrec-subst* t₂[σ₂]⇒*t₂′ ⊢A₂[σ₂] ⟩∎∷
        emptyrec p (A₂ [ σ₂ ]) (t₂ [ σ₂ ])             ∎

opaque

  -- Validity of equality between applications of emptyrec

  emptyrec-congᵛ :
    Γ ⊩ᵛ⟨ l ⟩ A₁ ≡ A₂ →
    Γ ⊩ᵛ⟨ l′ ⟩ t₁ ≡ t₂ ∷ Empty →
    Γ ⊩ᵛ⟨ l ⟩ emptyrec p A₁ t₁ ≡ emptyrec p A₂ t₂ ∷ A₁
  emptyrec-congᵛ A₁≡A₂ t₁≡t₂ =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( wf-⊩ᵛ≡ A₁≡A₂ .proj₁
      , λ ξ⊇ → ⊩emptyrec≡emptyrec (defn-wk-⊩ᵛ≡ ξ⊇ A₁≡A₂)
                                  (defn-wk-⊩ᵛ≡∷ ξ⊇ t₁≡t₂)
      )

opaque

  -- Validity of emptyrec.

  emptyrecᵛ :
    Γ ⊩ᵛ⟨ l ⟩ A →
    Γ ⊩ᵛ⟨ l′ ⟩ t ∷ Empty →
    Γ ⊩ᵛ⟨ l ⟩ emptyrec p A t ∷ A
  emptyrecᵛ ⊩A ⊩t =
    ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ $
    emptyrec-congᵛ (refl-⊩ᵛ≡ ⊩A) (refl-⊩ᵛ≡∷ ⊩t)
