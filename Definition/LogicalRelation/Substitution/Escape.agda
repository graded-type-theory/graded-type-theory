------------------------------------------------------------------------
-- Escaping the logical relation.
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Escape
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.Untyped M hiding (_∷_)
open import Definition.Untyped.Properties M

open import Definition.Typed R

open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.Properties R

open import Tools.Function
open import Tools.Nat
open import Tools.Product

private
  variable
    n : Nat
    Γ : Con Term n
    A B : Term n
    l : TypeLevel
    b : BinderMode
    p q : M
    [Γ] : ⊩ᵛ _

-- Valid types are well-formed.
escapeᵛ : ∀ {A l} ([Γ] : ⊩ᵛ Γ) → Γ ⊩ᵛ⟨ l ⟩ A / [Γ] → Γ ⊢ A
escapeᵛ [Γ] [A] =
  let ⊢Γ = soundContext [Γ]
      idSubst = idSubstS [Γ]
  in  escape (irrelevance′ (subst-id _) (proj₁ (unwrap [A] ⊢Γ idSubst)))

-- Valid type equality respects the equality relation.
escapeEqᵛ : ∀ {A B l} ([Γ] : ⊩ᵛ Γ) ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
              → Γ ⊩ᵛ⟨ l ⟩ A ≡ B / [Γ] / [A] → Γ ⊢ A ≅ B
escapeEqᵛ [Γ] [A] [A≡B] =
  let ⊢Γ = soundContext [Γ]
      idSubst = idSubstS [Γ]
      [idA]  = proj₁ (unwrap [A] ⊢Γ idSubst)
      [idA]′ = irrelevance′ (subst-id _) [idA]
  in  escapeEq [idA]′ (irrelevanceEq″ (subst-id _) (subst-id _)
                                           [idA] [idA]′ ([A≡B] ⊢Γ idSubst))

-- Valid terms are well-formed.
escapeTermᵛ : ∀ {t A l} ([Γ] : ⊩ᵛ Γ) ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
               → Γ ⊩ᵛ⟨ l ⟩ t ∷ A / [Γ] / [A] → Γ ⊢ t ∷ A
escapeTermᵛ [Γ] [A] [t] =
  let ⊢Γ = soundContext [Γ]
      idSubst = idSubstS [Γ]
      [idA]  = proj₁ (unwrap [A] ⊢Γ idSubst)
      [idA]′ = irrelevance′ (subst-id _) (proj₁ (unwrap [A] ⊢Γ idSubst))
  in  escapeTerm [idA]′
                    (irrelevanceTerm″ (subst-id _) (subst-id _)
                                       [idA] [idA]′ (proj₁ ([t] ⊢Γ idSubst)))

-- Valid term equality respects the equality relation.
escapeEqTermᵛ : ∀ {t u A l} ([Γ] : ⊩ᵛ Γ) ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
               → Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A / [Γ] / [A] → Γ ⊢ t ≅ u ∷ A
escapeEqTermᵛ [Γ] [A] [t≡u] =
  let ⊢Γ = soundContext [Γ]
      idSubst = idSubstS [Γ]
      [idA]  = proj₁ (unwrap [A] ⊢Γ idSubst)
      [idA]′ = irrelevance′ (subst-id _) (proj₁ (unwrap [A] ⊢Γ idSubst))
  in  escapeTermEq [idA]′
                       (irrelevanceEqTerm″ (subst-id _) (subst-id _)
                                            (subst-id _)
                                            [idA] [idA]′ ([t≡u] ⊢Γ idSubst))

-- If the type Unit is valid, then it is allowed.

⊩ᵛUnit→Unit-allowed :
  Γ ⊩ᵛ⟨ l ⟩ Unit / [Γ] →
  Unit-allowed
⊩ᵛUnit→Unit-allowed {Γ = Γ} {l = l} {[Γ] = [Γ]} =
  Γ ⊩ᵛ⟨ l ⟩ Unit / [Γ]                                        →⟨ (λ hyp _ σ → proj₁ (unwrap hyp _ σ)) ⟩
  ((⊢Γ : ⊢ Γ) → Γ ⊩ˢ idSubst ∷ Γ / [Γ] / ⊢Γ → Γ ⊩⟨ l ⟩ Unit)  →⟨ (_$ idSubstS _) ∘→ (_$ _) ⟩
  Γ ⊩⟨ l ⟩ Unit                                               →⟨ ⊩Unit→Unit-allowed ⟩
  Unit-allowed                                                □

-- If the type ΠΣ⟨ b ⟩ p , q ▷ A ▹ B is valid, then it is allowed.

⊩ᵛΠΣ→ΠΣ-allowed :
  Γ ⊩ᵛ⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B / [Γ] →
  ΠΣ-allowed b p q
⊩ᵛΠΣ→ΠΣ-allowed
  {Γ = Γ} {l = l} {b = b} {p = p} {q = q} {A = A} {B = B} {[Γ] = [Γ]} =
  Γ ⊩ᵛ⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B / [Γ]             →⟨ (λ hyp _ σ → proj₁ (unwrap hyp _ σ)) ⟩

  ((⊢Γ : ⊢ Γ) → Γ ⊩ˢ idSubst ∷ Γ / [Γ] / ⊢Γ →
   Γ ⊩⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B [ idSubst ])  →⟨ (_$ idSubstS _) ∘→ (_$ _) ⟩

  Γ ⊩⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B [ idSubst ]    →⟨ ⊩ΠΣ→ΠΣ-allowed ⟩

  ΠΣ-allowed b p q                             □
