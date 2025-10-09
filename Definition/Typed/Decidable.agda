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
open Type-restrictions R

open import Definition.Untyped M
open import Definition.Typed R
open import Definition.Typed.Consequences.Unfolding R
open import Definition.Typed.Properties R
open import Definition.Typed.Syntactic R
open import Definition.Typed.Variant
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
    Δ : Con Term n
    Γ : Cons m n
    A t : Term n

-- Re-export decidability of type and term equality
open import Definition.Typed.Decidable.Equality R _≟_ public

-- If Γ is well-formed and A is checkable, then Γ ⊢ A is decidable.

dec : ⊢ Γ → Checkable-type A → Dec (Γ ⊢ A)
dec ⊢Γ A =
  Dec.map (soundness⇇Type ⊢Γ) (completeness⇇Type A) (dec⇇Type ⊢Γ A)

-- Type-checking for well-formed types: if Γ ⊢ A holds and t is
-- checkable, then Γ ⊢ t ∷ A is decidable.

decTermᶜ : Γ ⊢ A → Checkable t → Dec (Γ ⊢ t ∷ A)
decTermᶜ ⊢A t = Dec.map soundness⇇ (completeness⇇ t) (dec⇇ t ⊢A)

-- Type-checking for arbitrary checkable types: if Γ is well-formed
-- and A and t are checkable, then Γ ⊢ t ∷ A is decidable.

decTermTypeᶜ : ⊢ Γ → Checkable-type A → Checkable t → Dec (Γ ⊢ t ∷ A)
decTermTypeᶜ ⊢Γ A t =
  case dec ⊢Γ A of λ where
    (yes ⊢A) → decTermᶜ ⊢A t
    (no ¬⊢A) → no (¬⊢A ∘→ syntacticTerm)

-- Type inference: if ⊢ Γ holds and t is inferable, then
-- ∃ λ A → Γ ⊢ t ∷ A is decidable.

decTermᵢ : ⊢ Γ → Inferable t → Dec (∃ λ A → Γ ⊢ t ∷ A)
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
--
-- If explicit unfolding is used, then there are *two* recursive calls
-- to decWfDCon in the case for opaque definitions. However, if
-- transitive unfolding is used, then there is only one such recursive
-- call.

decWfDCon : CheckableDCon ∇ → Dec (» ∇)
decWfDCon ε = yes ε
decWfDCon {∇ = _ ∙⟨ opa φ ⟩!} (∇ ∙ᶜᵒ⟨ ok ⟩[ t ∷ A ]) =
  case (decWfDCon ∇ ×-dec′ λ »∇ →
        dec (ε »∇) A) of λ where
    (no not) → no λ where
      ∙ᵒ⟨ _ , _ ⟩[ _ ∷ ⊢A ] → not (defn-wf (wf ⊢A) , ⊢A)
    (yes (»∇ , ⊢A)) →
      let _ , φ↜ = total-»↜ φ _
          cont   = λ »∇′ →
            let ⊢A′ = Unconditional.unfold-⊢ φ↜ (λ _ → »∇′) ⊢A in
            case decTermᶜ ⊢A′ t of λ where
              (no not) → no λ where
                ∙ᵒ⟨ _ , φ′↜ ⟩[ ⊢t ∷ _ ] →
                  not $
                  PE.subst₃ _⊢_∷_
                    (PE.cong (_» ε) (unique-»↜ φ′↜ φ↜)) PE.refl PE.refl
                    ⊢t
              (yes ⊢t) → yes ∙ᵒ⟨ ok , φ↜ ⟩[ ⊢t ∷ ⊢A ]
      in
      case PE.singleton unfolding-mode of λ where
        (transitive , ≡transitive) →
          cont (Transitive.unfold-» ≡transitive φ↜ »∇)
        (explicit , _) →
          case decWfDCon (unfold-Checkable φ↜ ∇) of λ where
            (no not) → no λ where
              ∙ᵒ⟨ _ , φ′↜ ⟩[ ⊢t ∷ _ ] →
                not $ defn-wf $ wfTerm $
                PE.subst₃ _⊢_∷_
                  (PE.cong (_» ε) (unique-»↜ φ′↜ φ↜)) PE.refl PE.refl
                  ⊢t
            (yes »∇′) → cont »∇′
decWfDCon (∇ ∙ᶜᵗ[ t ∷ A ]) =
  case (decWfDCon ∇ ×-dec′ λ »∇ →
        dec (ε »∇) A ×-dec′ λ ⊢A →
        decTermᶜ ⊢A t) of λ where
    (no not) → no λ where
      ∙ᵗ[ ⊢t ] → not (defn-wf (wfTerm ⊢t) , wf-⊢∷ ⊢t , ⊢t)
    (yes (_ , _ , ⊢t)) → yes ∙ᵗ[ ⊢t ]

-- If » ∇ and Δ is a checkable context, then ∇ »⊢ Δ is decidable.

decWfCon : » ∇ → CheckableCon Δ → Dec (∇ »⊢ Δ)
decWfCon »∇ ε = yes (ε »∇)
decWfCon »∇ (Δ ∙ A) = case decWfCon »∇ Δ of λ where
  (yes ⊢Δ) → case dec ⊢Δ A of λ where
    (yes ⊢A) → yes (∙ ⊢A)
    (no ⊬A) → no λ where
      (∙ ⊢A) → ⊬A ⊢A
  (no ⊬Δ) → no λ where
    (∙ ⊢A) → ⊬Δ (wf ⊢A)

opaque
  unfolding CheckableCons

  -- If Γ is checkable, then ⊢ Γ is decidable.

  decWfCons : CheckableCons Γ → Dec (⊢ Γ)
  decWfCons (∇ , Γ) =
    case decWfDCon ∇ of λ where
      (no not) → no λ ⊢Γ → not (defn-wf ⊢Γ)
      (yes »∇) → decWfCon »∇ Γ

-- If Γ and A are checkable, then Γ ⊢ A is decidable.

decConTypeᶜ :
  CheckableCons Γ → Checkable-type A → Dec (Γ ⊢ A)
decConTypeᶜ Γ A =
  case decWfCons Γ of λ where
    (yes ⊢Γ) → dec ⊢Γ A
    (no ¬⊢Γ) → no (¬⊢Γ ∘→ wf)

-- Type-checking for arbitrary checkable contexts and types: if Γ, A
-- and t are checkable, then Γ ⊢ t ∷ A is decidable.

decConTermTypeᶜ :
  CheckableCons Γ → Checkable-type A → Checkable t → Dec (Γ ⊢ t ∷ A)
decConTermTypeᶜ Γ A t =
  case decWfCons Γ of λ where
    (yes ⊢Γ) → decTermTypeᶜ ⊢Γ A t
    (no ¬⊢Γ) → no (¬⊢Γ ∘→ wfTerm)

-- Type inference for arbitrary checkable contexts: if Γ is checkable
-- and t is inferable, then ∃ λ A → Γ ⊢ t ∷ A is decidable.

decConTermᵢ :
  CheckableCons Γ → Inferable t → Dec (∃ λ A → Γ ⊢ t ∷ A)
decConTermᵢ Γ t =
  case decWfCons Γ of λ where
    (yes ⊢Γ) → decTermᵢ ⊢Γ t
    (no ¬⊢Γ) → no (¬⊢Γ ∘→ wfTerm ∘→ proj₂)
