------------------------------------------------------------------------
-- Decidability of typing.
------------------------------------------------------------------------

open import Definition.Typechecking.Decidable.Assumptions
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Decidable
  {a} {M : Set a}
  {𝕄 : Modality M}
  {R : Type-restrictions 𝕄}
  (as : Assumptions R)
  where

open Assumptions as

open import Definition.Untyped M
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Syntactic R
open import Definition.Typed.Well-formed R
open import Definition.Typechecking R
open import Definition.Typechecking.Soundness R
open import Definition.Typechecking.Completeness R
open import Definition.Typechecking.Decidable as

open import Tools.Function
open import Tools.Nat using (Nat)
import Tools.PropositionalEquality as PE
open import Tools.Product
open import Tools.Relation as Dec

private
  variable
    m n : Nat
    ∇ ∇′ : DCon (Term 0) m
    φ : Unfolding _
    Γ : Con Term n
    A t : Term n

-- Re-export decidability of type and term equality
open import Definition.Typed.Decidable.Equality R _≟_ public

-- If Γ is well-formed and A is checkable, then ∇ » Γ ⊢ A is decidable.

dec : ∇ »⊢ Γ → Checkable-type A → Dec (∇ » Γ ⊢ A)
dec ⊢Γ A =
  Dec.map (soundness⇇Type ⊢Γ) (completeness⇇Type A) (dec⇇Type ⊢Γ A)

-- Type-checking for well-formed types: if ∇ » Γ ⊢ A holds and t is
-- checkable, then ∇ » Γ ⊢ t ∷ A is decidable.

decTermᶜ : ∇ » Γ ⊢ A → Checkable t → Dec (∇ » Γ ⊢ t ∷ A)
decTermᶜ ⊢A t = Dec.map soundness⇇ (completeness⇇ t) (dec⇇ t ⊢A)

-- Type-checking for arbitrary checkable types: if Γ is well-formed
-- and A and t are checkable, then ∇ » Γ ⊢ t ∷ A is decidable.

decTermTypeᶜ : ∇ »⊢ Γ → Checkable-type A → Checkable t → Dec (∇ » Γ ⊢ t ∷ A)
decTermTypeᶜ ⊢Γ A t =
  case dec ⊢Γ A of λ where
    (yes ⊢A) → decTermᶜ ⊢A t
    (no ¬⊢A) → no (¬⊢A ∘→ syntacticTerm)

-- Type inference: if ⊢ Γ holds and t is inferable, then
-- ∃ λ A → ∇ » Γ ⊢ t ∷ A is decidable.

decTermᵢ : ∇ »⊢ Γ → Inferable t → Dec (∃ λ A → ∇ » Γ ⊢ t ∷ A)
decTermᵢ ⊢Γ t = Dec.map
  (λ { (A , t⇉A) → A , (proj₂ (soundness⇉ ⊢Γ t⇉A))})
  (λ { (A , ⊢t)  → _ , (proj₁ (proj₂ (completeness⇉ t ⊢t)))})
  (dec⇉ ⊢Γ t)

-- Checkability of definition contexts is preserved under unfolding.

unfold-Checkable : φ » ∇′ ↜ ∇ → CheckableDCon ∇ → CheckableDCon ∇′
unfold-Checkable ε      ε                      = ε
unfold-Checkable (φ ⁰)  (∇ ∙ᶜᵒ⟨ ok ⟩[ t ∷ A ]) = unfold-Checkable φ ∇ ∙ᶜᵒ⟨ ok ⟩[ t ∷ A ]
unfold-Checkable (φ ⁰)  (∇ ∙ᶜᵗ[ t ∷ A ])       = unfold-Checkable φ ∇       ∙ᶜᵗ[ t ∷ A ]
unfold-Checkable (φ ¹ᵒ) (∇ ∙ᶜᵒ⟨ ok ⟩[ t ∷ A ]) = unfold-Checkable φ ∇       ∙ᶜᵗ[ t ∷ A ]
unfold-Checkable (φ ¹ᵗ) (∇ ∙ᶜᵗ[ t ∷ A ])       = unfold-Checkable φ ∇       ∙ᶜᵗ[ t ∷ A ]

-- If ∇ is a checkable definition context, then » ∇ is decidable.

decWfDCon : CheckableDCon ∇ → Dec (» ∇)
decWfDCon ε = yes ε
decWfDCon {∇ = _ ∙⟨ opa φ ⟩[ _ ∷ _ ]} (∇ ∙ᶜᵒ⟨ ok ⟩[ t ∷ A ]) =
  case decWfDCon ∇ of λ where
    (no not) → no λ where
      ∙ᵒ⟨ _ , _ ⟩[ _ ∷ ⊢A ] → not (defn-wf (wf ⊢A))
    (yes »∇) → case dec (ε »∇) A of λ where
      (no not) → no λ where
        ∙ᵒ⟨ _ , _ ⟩[ _ ∷ ⊢A ] → not ⊢A
      (yes ⊢A) → let _ , φ↜ = total-»↜ φ _ in
        case decWfDCon (unfold-Checkable φ↜ ∇) of λ where
          (no not) → no λ where
            ∙ᵒ⟨ _ , φ′↜ ⟩[ ⊢t ∷ _ ] → not $ defn-wf $ wfTerm $
              PE.subst (_» ε ⊢ _ ∷ _) (unique-»↜ φ′↜ φ↜) ⊢t
          (yes »∇′) → case dec (ε »∇′) A of λ where
            (no not) → no λ where
              ∙ᵒ⟨ _ , φ′↜ ⟩[ ⊢t ∷ _ ] → not $ wf-⊢∷ $
                PE.subst (_» ε ⊢ _ ∷ _) (unique-»↜ φ′↜ φ↜) ⊢t
            (yes ⊢A′) → case decTermᶜ ⊢A′ t of λ where
              (no not) → no λ where
                ∙ᵒ⟨ _ , φ′↜ ⟩[ ⊢t ∷ _ ] → not $
                  PE.subst (_» ε ⊢ _ ∷ _) (unique-»↜ φ′↜ φ↜) ⊢t
              (yes ⊢t) → yes ∙ᵒ⟨ ok , φ↜ ⟩[ ⊢t ∷ ⊢A ]
decWfDCon (∇ ∙ᶜᵗ[ t ∷ A ]) =
  case decWfDCon ∇ of λ where
    (no not) → no λ where
      ∙ᵗ[ ⊢t ] → not (defn-wf (wfTerm ⊢t))
    (yes »∇) → case dec (ε »∇) A of λ where
      (no not) → no λ where
        ∙ᵗ[ ⊢t ] → not (wf-⊢∷ ⊢t)
      (yes ⊢A) → case decTermᶜ ⊢A t of λ where
        (no not) → no λ where
          ∙ᵗ[ ⊢t ] → not ⊢t
        (yes ⊢t) → yes ∙ᵗ[ ⊢t ]

-- If » ∇ and Γ is a checkable context, then ∇ »⊢ Γ is decidable.

decWfCon : » ∇ → CheckableCon Γ → Dec (∇ »⊢ Γ)
decWfCon »∇ ε = yes (ε »∇)
decWfCon »∇ (Γ ∙ A) = case decWfCon »∇ Γ of λ where
  (yes ⊢Γ) → case dec ⊢Γ A of λ where
    (yes ⊢A) → yes (∙ ⊢A)
    (no ⊬A) → no λ where
      (∙ ⊢A) → ⊬A ⊢A
  (no ⊬Γ) → no λ where
    (∙ ⊢A) → ⊬Γ (wf ⊢A)

-- If ∇ and Γ are checkable, then ∇ »⊢ Γ is decidable.

decWfCons : CheckableDCon ∇ → CheckableCon Γ → Dec (∇ »⊢ Γ)
decWfCons ∇ Γ =
  case decWfDCon ∇ of λ where
    (no not) → no λ ⊢Γ → not (defn-wf ⊢Γ)
    (yes »∇) → decWfCon »∇ Γ

-- If ∇, Γ, and A are checkable, then ∇ » Γ ⊢ A is decidable.

decConTypeᶜ :
  CheckableDCon ∇ → CheckableCon Γ →
  Checkable-type A → Dec (∇ » Γ ⊢ A)
decConTypeᶜ ∇ Γ A =
  case decWfCons ∇ Γ of λ where
    (yes ⊢Γ) → dec ⊢Γ A
    (no ¬⊢Γ) → no (¬⊢Γ ∘→ wf)

-- Type-checking for arbitrary checkable contexts and types: if ∇, Γ, A
-- and t are checkable, then ∇ » Γ ⊢ t ∷ A is decidable.

decConTermTypeᶜ :
  CheckableDCon ∇ → CheckableCon Γ →
  Checkable-type A → Checkable t → Dec (∇ » Γ ⊢ t ∷ A)
decConTermTypeᶜ ∇ Γ A t =
  case decWfCons ∇ Γ of λ where
    (yes ⊢Γ) → decTermTypeᶜ ⊢Γ A t
    (no ¬⊢Γ) → no (¬⊢Γ ∘→ wfTerm)

-- Type inference for arbitrary checkable contexts: if ∇ and Γ are
-- checkable and t is inferable, then ∃ λ A → ∇ » Γ ⊢ t ∷ A is decidable.

decConTermᵢ :
  CheckableDCon ∇ → CheckableCon Γ →
  Inferable t → Dec (∃ λ A → ∇ » Γ ⊢ t ∷ A)
decConTermᵢ ∇ Γ t =
  case decWfCons ∇ Γ of λ where
    (yes ⊢Γ) → decTermᵢ ⊢Γ t
    (no ¬⊢Γ) → no (¬⊢Γ ∘→ wfTerm ∘→ proj₂)
