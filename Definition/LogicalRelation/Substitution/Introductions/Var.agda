------------------------------------------------------------------------
-- Validity of variables.
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Introductions.Var
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}

open import Definition.Untyped M
open import Definition.Untyped.Properties M
open import Definition.Typed R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.Substitution R
import Definition.LogicalRelation.Substitution.Irrelevance R as IS

open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    Γ : Con Term _

-- Fundamental theorem for variables.
fundamentalVar : ∀ {A x}
               → x ∷ A ∈ Γ
               → ([Γ] : ⊩ᵛ Γ)
               → ∃ λ ([A] : Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ])
               → Γ ⊩ᵛ⟨ ¹ ⟩ var x ∷ A / [Γ] / [A]
fundamentalVar here (_∙_ {A = A} {l = l} [Γ] [A]) =
  (wrap λ ⊢Δ [σ] →
     let [σA]  = proj₁ (unwrap [A] ⊢Δ (proj₁ [σ]))
         [σA′] = maybeEmb (irrelevance′ (PE.sym (subst-wk A)) [σA])
     in  [σA′]
     ,   (λ [σ′] [σ≡σ′] →
            irrelevanceEq″ (PE.sym (subst-wk A)) (PE.sym (subst-wk A))
                            [σA] [σA′] (proj₂ (unwrap [A] ⊢Δ (proj₁ [σ]))
                                              (proj₁ [σ′]) (proj₁ [σ≡σ′]))))
  , (λ ⊢Δ [σ] →
       let [σA]  = proj₁ (unwrap [A] ⊢Δ (proj₁ [σ]))
           [σA′] = maybeEmb (irrelevance′ (PE.sym (subst-wk A)) [σA])
       in  irrelevanceTerm′ (PE.sym (subst-wk A)) [σA] [σA′] (proj₂ [σ])
       ,   (λ [σ′] [σ≡σ′] → irrelevanceEqTerm′ (PE.sym (subst-wk A))
                                               [σA] [σA′] (proj₂ [σ≡σ′])))
fundamentalVar (there {A = A} h) ([Γ] ∙ [B]) =
  (wrap λ ⊢Δ [σ] →
     let [h]   = unwrap (proj₁ (fundamentalVar h [Γ])) ⊢Δ (proj₁ [σ])
         [σA]  = proj₁ [h]
         [σA′] = irrelevance′ (PE.sym (subst-wk A)) [σA]
     in  [σA′]
     ,   (λ [σ′] [σ≡σ′] →
            irrelevanceEq″ (PE.sym (subst-wk A)) (PE.sym (subst-wk A))
                            [σA] [σA′]
                            (proj₂ [h] (proj₁ [σ′]) (proj₁ [σ≡σ′]))))
  , (λ ⊢Δ [σ] →
       let [h]   = unwrap (proj₁ (fundamentalVar h [Γ])) ⊢Δ (proj₁ [σ])
           [σA]  = proj₁ [h]
           [σA′] = irrelevance′ (PE.sym (subst-wk A)) [σA]
           [h′] = (proj₂ (fundamentalVar h [Γ])) ⊢Δ (proj₁ [σ])
       in  irrelevanceTerm′ (PE.sym (subst-wk A)) [σA] [σA′] (proj₁ [h′])
       ,   (λ [σ′] [σ≡σ′] →
              irrelevanceEqTerm′ (PE.sym (subst-wk A)) [σA] [σA′]
                                 (proj₂ [h′] (proj₁ [σ′]) (proj₁ [σ≡σ′]))))

opaque

  varᵛ : ∀ {A x l}
       → x ∷ A ∈ Γ
       → ([Γ] : ⊩ᵛ Γ)
       → ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
       → Γ ⊩ᵛ⟨ l ⟩ var x ∷ A / [Γ] / [A]
  varᵛ d [Γ] [A] =
    let [A]′ , [x] = fundamentalVar d [Γ]
    in  IS.irrelevanceTerm [Γ] [Γ] [A]′ [A] [x]
