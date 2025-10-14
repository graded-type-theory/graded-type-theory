------------------------------------------------------------------------
-- Some admissible rules related to Σ
------------------------------------------------------------------------

-- Note that lemmas corresponding to the lemmas in this module, in one
-- case with fewer arguments, can (at the time of writing) be imported
-- from Definition.Typed.Properties.Admissible.Sigma.

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Properties.Admissible.Sigma.Primitive
  {ℓ} {M : Set ℓ}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Properties.Admissible.Lift.Primitive R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Substitution.Primitive.Primitive R
open import Definition.Typed.Weakening R

open import Definition.Untyped M
open import Definition.Untyped.Pi-Sigma M
open import Definition.Untyped.Properties M
open import Definition.Untyped.Sigma 𝕄

open import Tools.Function
import Tools.PropositionalEquality as PE

private variable
  Γ                         : Con _ _
  A B l₁ l₂ t t₁ t₂ u u₁ u₂ : Term _
  p q                       : M
  s                         : Strength

------------------------------------------------------------------------
-- Some typing and equality rules related to Σʰ⟨_⟩

opaque
  unfolding ΠΣʰ prodʰ

  -- A typing rule for prodʰ.

  prodʰⱼ :
    Γ ⊢ l₁ ∷ Level →
    Γ ⊢ l₂ ∷ Level →
    Γ ∙ A ⊢ B →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Σ-allowed s p q →
    Γ ⊢ prodʰ s p t u ∷ Σʰ⟨ s ⟩ p q l₁ l₂ A B
  prodʰⱼ ⊢l₁ ⊢l₂ ⊢B ⊢t ⊢u ok =
    let ⊢A = ⊢∙→⊢ (wf ⊢B) in
    prodⱼ (Liftⱼ (wkTerm₁ (Liftⱼ ⊢l₂ ⊢A) ⊢l₁) (lower₀Type ⊢l₂ ⊢B))
      (liftⱼ ⊢l₂ ⊢A ⊢t)
      (liftⱼ (PE.subst (_ ⊢_∷ _) (PE.sym (wk1-sgSubst _ _)) ⊢l₁)
         (⊢lower₀[lift]₀ ⊢B ⊢t) (conv ⊢u (sym (lower₀[lift]₀ ⊢B ⊢t))))
      ok

opaque
  unfolding ΠΣʰ prodʰ

  -- An equality rule for prodʰ.

  prodʰ-cong :
    Γ ⊢ l₁ ∷ Level →
    Γ ⊢ l₂ ∷ Level →
    Γ ∙ A ⊢ B →
    Γ ⊢ t₁ ∷ A →
    Γ ⊢ t₂ ∷ A →
    Γ ⊢ t₁ ≡ t₂ ∷ A →
    Γ ⊢ u₁ ∷ B [ t₁ ]₀ →
    Γ ⊢ u₂ ∷ B [ t₁ ]₀ →
    Γ ⊢ u₁ ≡ u₂ ∷ B [ t₁ ]₀ →
    Σ-allowed s p q →
    Γ ⊢ prodʰ s p t₁ u₁ ≡ prodʰ s p t₂ u₂ ∷ Σʰ⟨ s ⟩ p q l₁ l₂ A B
  prodʰ-cong ⊢l₁ ⊢l₂ ⊢B ⊢t₁ ⊢t₂ t₁≡t₂ ⊢u₁ ⊢u₂ u₁≡u₂ ok =
    let ⊢A      = ⊢∙→⊢ (wf ⊢B)
        B[t₁]₀≡ = sym (lower₀[lift]₀ ⊢B ⊢t₁)
    in
    prod-cong (Liftⱼ (wkTerm₁ (Liftⱼ ⊢l₂ ⊢A) ⊢l₁) (lower₀Type ⊢l₂ ⊢B))
      (lift-cong ⊢l₂ ⊢A ⊢t₁ ⊢t₂ t₁≡t₂)
      (lift-cong
         (PE.subst (flip (_⊢_∷_ _) _) (PE.sym $ wk1-sgSubst _ _) ⊢l₁)
         (⊢lower₀[lift]₀ ⊢B ⊢t₁) (conv ⊢u₁ B[t₁]₀≡) (conv ⊢u₂ B[t₁]₀≡)
         (conv u₁≡u₂ B[t₁]₀≡))
      ok
