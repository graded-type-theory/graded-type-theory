------------------------------------------------------------------------
-- The typing relation is an instance of the abstract set of
-- equality relations.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.EqRelInstance
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Weakening R
open import Definition.Typed.Well-formed R
open import Definition.Typed.EqualityRelation R
import Definition.Typed.EqualityRelation.Instance

open import Tools.Function
open import Tools.Product

private opaque

  -- A lemma used below.

  equality-relations :
    Equality-relations
      _⊢_≡_ _⊢_≡_∷_ _⊢_≡_∷Level _⊢_≡_∷_ No-equality-reflection
  equality-relations = λ where
      .Neutrals-included? →
        No-equality-reflection?
      .Equality-reflection-allowed→¬Neutrals-included →
        λ { ok (no-equality-reflection not-ok) → not-ok ok }
      .⊢≡→⊢≅                     → λ _ → idᶠ
      .⊢≡∷→⊢≅∷                   → λ _ → idᶠ
      .~-to-≅ₜ                   → idᶠ
      .⊢≅∷→⊢≅∷L                  → term-⊢≡∷
      .≅-eq                      → idᶠ
      .≅ₜ-eq                     → idᶠ
      .⊢≅∷L→⊢≡∷L                 → idᶠ
      .Level-literal→⊢≅∷L        → literal
      .⊢≅∷L→⊢≅∷                  → ⊢≡∷Level→⊢≡∷Level
      .≅-univ                    → univ
      .≅-sym                     → sym
      .≅ₜ-sym                    → sym′
      .~-sym                     → sym′
      .≅-trans                   → trans
      .≅ₜ-trans                  → trans
      .~-trans                   → trans
      .≅-conv                    → conv
      .~-conv                    → conv
      .≅-wk                      → wkEq
      .≅ₜ-wk                     → wkEqTerm
      .wk-⊢≅∷L                   → wkEqLevel
      .~-wk                      → wkEqTerm
      .≅-red (A⇒* , _) (B⇒* , _) →
        reduction A⇒* B⇒*
      .≅ₜ-red (A⇒* , _) (t⇒* , _) (u⇒* , _) →
        reductionₜ A⇒* t⇒* u⇒*
      .≅ₜ-Levelrefl → λ ⊢Γ ok → refl (Levelⱼ ⊢Γ ok)
      .≅-Levelrefl  → λ ok ⊢Γ → refl (Levelⱼ′ ok ⊢Γ)
      .≅ₜ-zeroᵘrefl → λ ok ⊢Γ → refl (zeroᵘⱼ ok ⊢Γ)
      .≅ₜ-sucᵘ-cong → sucᵘ-cong
      .≅ₜ-supᵘ-cong → supᵘ-cong
      .≅ₜ-supᵘ-zeroʳ → supᵘ-zeroʳⱼ ∘ᶠ ⊢≡→⊢
      .≅ₜ-supᵘ-assoc → λ a b c → supᵘ-assoc (⊢≡→⊢ a) (⊢≡→⊢ b) (⊢≡→⊢ c)
      .≅ₜ-supᵘ-comm → λ a b → supᵘ-comm (⊢≡→⊢ a) (⊢≡→⊢ b)
      .≅ₜ-supᵘ-idem → λ a → supᵘ-idem (⊢≡→⊢ a)
      .≅ₜ-supᵘ-sub  → λ a → supᵘ-sub (⊢≡→⊢ a)
      .≅ₜ-U-cong    → U-cong-⊢≡∷
      .≅-Lift-cong  → Lift-cong
      .≅ₜ-Lift-cong → Lift-cong′
      .≅-Lift-η     → λ ⊢t ⊢u _ _ lt≡lu → Lift-η′ ⊢t ⊢u lt≡lu
      .≅ₜ-ℕrefl     → refl ∘ᶠ ℕⱼ
      .≅ₜ-Emptyrefl → refl ∘ᶠ Emptyⱼ
      .≅ₜ-Unit-refl → λ ⊢Γ ok → refl (Unitⱼ ⊢Γ ok)
      .≅ₜ-η-unit    → η-unit
      .≅-ΠΣ-cong    → ΠΣ-cong
      .≅ₜ-ΠΣ-cong   → ΠΣ-cong
      .≅ₜ-zerorefl  → refl ∘ᶠ zeroⱼ
      .≅-suc-cong   → suc-cong
      .≅-prod-cong  → prod-cong
      .≅-η-eq       → λ ⊢t ⊢u _ _ t0≡u0 → η-eq′ ⊢t ⊢u t0≡u0
      .≅-Σ-η        → λ ⊢t ⊢u _ _ fst≡ snd≡ → Σ-η′ ⊢t ⊢u fst≡ snd≡
      .~-var        → refl
      .~-lower      → lower-cong
      .~-app        → app-cong
      .~-fst        → fst-cong
      .~-snd        → snd-cong
      .~-natrec     → natrec-cong
      .~-prodrec    → prodrec-cong
      .~-emptyrec   → emptyrec-cong
      .~-unitrec    → unitrec-cong
      .≅ₜ-star-refl → λ ⊢Γ ok → refl (starⱼ ⊢Γ ok)
      .≅-Id-cong    → Id-cong
      .≅ₜ-Id-cong   → Id-cong
      .≅ₜ-rflrefl   → refl ∘ᶠ rflⱼ
      .~-J          → J-cong
      .~-K          → K-cong
      .~-[]-cong    → []-cong-cong
    where
    open Equality-relations

-- An EqRelSet instance that uses definitional equality (_⊢_≡_,
-- _⊢_≡_∷_ and _⊢_≡_∷Level). Neutrals are included if and only if
-- equality reflection is not allowed.

instance

  eqRelInstance : EqRelSet
  eqRelInstance = λ where
    .EqRelSet._⊢_≅_              → _⊢_≡_
    .EqRelSet._⊢_≅_∷_            → _⊢_≡_∷_
    .EqRelSet._⊢_≅_∷Level        → _⊢_≡_∷Level
    .EqRelSet._⊢_~_∷_            → _⊢_≡_∷_
    .EqRelSet.Neutrals-included  → No-equality-reflection
    .EqRelSet.equality-relations → equality-relations

open EqRelSet eqRelInstance public
