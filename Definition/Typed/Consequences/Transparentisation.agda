------------------------------------------------------------------------
-- Typing is not necessarily preserved by transparentisation
------------------------------------------------------------------------

open import Definition.Typed.Variant
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Consequences.Transparentisation
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant hiding (ℕ≢ne)

open import Definition.Typed R
open import Definition.Typed.Consequences.Inequality R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Well-formed R

open import Tools.Function
import Tools.Level as L
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Unit
open import Tools.Vec using (ε)

opaque
  unfolding Trans

  -- If the unfolding mode is "explicit", then the
  -- transparentisation of a well-formed definition context might
  -- not be well-formed.

  no-unfold-» :
    unfolding-mode PE.≡ explicit →
    Opacity-allowed →
    ∃₂ λ (∇ : DCon (Term 0) 2) (φ : Unfolding 2) →
      » ∇ × ¬ » Trans φ ∇
  no-unfold-» mode-eq ok =
    let ∇₁ = ε ∙⟨ opa ε ⟩[ ℕ ∷ U zeroᵘ ]
        ∇ = ∇₁ ∙⟨ opa (ε ¹) ⟩[ zero ∷ defn 0 ]
        ∇₁⊢ε = ε ∙ᵒ⟨ ok ⟩[ ℕⱼ εε ∷ ⊢U (⊢zeroᵘ εε) ]
        ∇₁ᵗ⊢ε = ε ∙ᵗ[ ℕⱼ εε ]
        »∇ = ∙ᵒ⟨ ok ⟩[
          conv (zeroⱼ ∇₁ᵗ⊢ε) (sym (univ (δ-red ∇₁ᵗ⊢ε here PE.refl PE.refl))) ∷
          univ (defn ∇₁⊢ε here PE.refl) ]
        not »Trans-∇ =
          ℕ≢ne {V = L.Lift _ ⊤} ⦃ ok = ε ⦄
            (defn
               (there
                  (PE.subst (_↦⊘∷_∈_ _ (U zeroᵘ) ∘→ flip Trans _)
                     (PE.sym $ ⊔ᵒᵗ≡const mode-eq) here)))
            (sym (inversion-zero (wf-↦∷∈ here »Trans-∇)))
    in  ∇ , ε ⁰ ¹ , »∇ , not
