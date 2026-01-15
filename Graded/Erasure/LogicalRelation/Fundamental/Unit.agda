------------------------------------------------------------------------
-- Graded.Erasure validity of the unit type.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Erasure.LogicalRelation.Assumptions
open import Graded.Modality
open import Graded.Mode.Instances.Zero-one.Variant

module Graded.Erasure.LogicalRelation.Fundamental.Unit
  {a} {M : Set a}
  {𝕄 : Modality M}
  (open Modality 𝕄)
  {R : Type-restrictions 𝕄}
  (variant : Mode-variant 𝕄)
  (as : Assumptions R)
  ⦃ 𝟘-well-behaved : Has-well-behaved-zero M 𝕄 ⦄
  where

open Assumptions as
open Type-restrictions R

open import Graded.Modality.Properties.Has-well-behaved-zero 𝕄

open import Graded.Erasure.LogicalRelation as
open import Graded.Erasure.LogicalRelation.Assumptions.Reasoning
  is-reduction-relation
open import Graded.Erasure.LogicalRelation.Hidden variant as

open import Graded.Erasure.Extraction 𝕄
open import Graded.Erasure.Extraction.Properties 𝕄

import Graded.Erasure.Target as T
import Graded.Erasure.Target.Properties as TP
import Graded.Erasure.Target.Reasoning

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M
open import Definition.Untyped.Whnf M type-variant

open import Definition.Typed R
open import Definition.Typed.Consequences.Inequality R
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Consequences.Reduction R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Reasoning.Term R
open import Definition.Typed.Substitution R
open import Definition.Typed.Syntactic R

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Mode.Instances.Zero-one variant

open import Tools.Empty
open import Tools.Function
open import Tools.Nat
open import Tools.Product
open import Tools.Sum
import Tools.PropositionalEquality as PE
open import Tools.Relation

private
  variable
    n : Nat
    γ δ : Conₘ n
    Γ : Con Term n
    A t u : Term n
    m : Mode
    s : Strength
    l : Universe-level
    p q : M

opaque

  -- Validity of Unit.

  Unitʳ : γ ▸ Γ ⊩ʳ Unit s l ∷[ m ∣ n ] U l
  Unitʳ =
    ▸⊩ʳ∷⇔ .proj₂ λ _ _ →
    ®∷→®∷◂ (®∷U⇔ .proj₂ (Uᵣ (λ { PE.refl → T.refl })))

opaque

  -- Validity of star.

  starʳ :
    Unit-allowed s →
    γ ▸ Γ ⊩ʳ star s l ∷[ m ∣ n ] Unit s l
  starʳ ok =
    ▸⊩ʳ∷⇔ .proj₂ λ _ _ →
    ®∷→®∷◂ (®∷Unit⇔ .proj₂ (starᵣ (⇒*→⇛ (id (starⱼ ⊢Δ ok))) T.refl))

opaque

  -- Validity of unitrec.

  unitrecʳ :
    ts » Γ ∙ Unitʷ l ⊢ A →
    ts » Γ ⊢ t ∷ Unitʷ l →
    ts » Γ ⊢ u ∷ A [ starʷ l ]₀ →
    γ ▸ Γ ⊩ʳ t ∷[ m ᵐ· p ∣ n ] Unitʷ l →
    δ ▸ Γ ⊩ʳ u ∷[ m ∣ n ] A [ starʷ l ]₀ →
    (p PE.≡ 𝟘 → Empty-con Δ × Transparent ts ⊎ Unitʷ-η) →
    p ·ᶜ γ +ᶜ δ ▸ Γ ⊩ʳ unitrec l p q A t u ∷[ m ∣ n ] A [ t ]₀
  unitrecʳ {m = 𝟘ᵐ} _ _ _ _ _ _ =
    ▸⊩ʳ∷[𝟘ᵐ]
  unitrecʳ
    {Γ} {l} {A} {t} {u} {γ} {m = 𝟙ᵐ} {p} {n} {δ} {q}
    ⊢A ⊢t ⊢u ⊩ʳt ⊩ʳu p≡𝟘→ =
    ▸⊩ʳ∷⇔ .proj₂ λ {σ = σ} {σ′ = σ′} ⊢σ σ®σ′ →
    case
      (λ p≢𝟘 →
         case PE.sym $ ≢𝟘→⌞⌟≡𝟙ᵐ p≢𝟘 of λ
           𝟙ᵐ≡⌞p⌟ →                                            $⟨ σ®σ′ ⟩

         σ ® σ′ ∷[ 𝟙ᵐ ∣ n ] Γ ◂ p ·ᶜ γ +ᶜ δ                    →⟨ (subsumption-®∷[∣]◂ λ x →

           (p ·ᶜ γ +ᶜ δ) ⟨ x ⟩ PE.≡ 𝟘                                →⟨ proj₁ ∘→ +ᶜ-positive-⟨⟩ (_ ·ᶜ γ) ⟩
           (p ·ᶜ γ) ⟨ x ⟩ PE.≡ 𝟘                                     →⟨ ·ᶜ-zero-product-⟨⟩ γ ⟩
           p PE.≡ 𝟘 ⊎ γ ⟨ x ⟩ PE.≡ 𝟘                                 →⟨ (λ { (inj₁ p≡𝟘)    → ⊥-elim (p≢𝟘 p≡𝟘)
                                                                           ; (inj₂ γ⟨x⟩≡𝟘) → γ⟨x⟩≡𝟘
                                                                           }) ⟩
           γ ⟨ x ⟩ PE.≡ 𝟘                                            □) ⟩

         σ ® σ′ ∷[ 𝟙ᵐ ∣ n ] Γ ◂ γ                              ≡⟨ PE.cong₄ (_®_∷[_∣_]_◂_ _ _) 𝟙ᵐ≡⌞p⌟ PE.refl PE.refl PE.refl ⟩→

         σ ® σ′ ∷[ ⌞ p ⌟ ∣ n ] Γ ◂ γ                           →⟨ ▸⊩ʳ∷⇔ .proj₁ ⊩ʳt ⊢σ ⟩

         t [ σ ] ® erase str t T.[ σ′ ] ∷ Unitʷ l ◂ ⌜ ⌞ p ⌟ ⌝  →⟨ ®∷→®∷◂ω (non-trivial ∘→ PE.trans (PE.cong ⌜_⌝ 𝟙ᵐ≡⌞p⌟)) ⟩

         t [ σ ] ® erase str t T.[ σ′ ] ∷ Unitʷ l              ⇔⟨ ®∷Unit⇔ ⟩→

         t [ σ ] ® erase str t T.[ σ′ ] ∷Unit⟨ 𝕨 , l ⟩         □)
    of λ
      p≢𝟘→t[σ]®t[σ′] →

    case
      (let open Graded.Erasure.Target.Reasoning in
       case is-𝟘? p of λ where
         (yes p≡𝟘) →
           erase str (unitrec l p q A t u) T.[ σ′ ]  ≡⟨ PE.cong T._[ _ ] $ unitrec-𝟘 l q A p≡𝟘 ⟩⇒
           erase str u T.[ σ′ ]                      ∎⇒
         (no p≢𝟘) →
           case p≢𝟘→t[σ]®t[σ′] p≢𝟘 of λ {
             (starᵣ _ t[σ′]⇒⋆) →
           erase str (unitrec l p q A t u) T.[ σ′ ]        ≡⟨ PE.cong T._[ _ ] $ unitrec-ω l q A p≢𝟘 ⟩⇒
           T.unitrec (erase str t) (erase str u) T.[ σ′ ]  ⇒*⟨ TP.unitrec-subst* t[σ′]⇒⋆ ⟩
           T.unitrec T.star (erase str u) T.[ σ′ ]         ⇒⟨ T.unitrec-β ⟩
           erase str u T.[ σ′ ]                            ∎⇒ })
    of λ
      unitrec⇒u[σ′] →
    case subst-⊢-⇑ ⊢A ⊢σ of λ
      ⊢A[σ⇑] →

    case
      (λ
         (t[σ]≡⋆ : ts » Δ ⊢ t [ σ ] ≡ starʷ l ∷ Unitʷ l)
         unitrec⇛u[σ] →                                                   $⟨ σ®σ′ ⟩

         σ ® σ′ ∷[ 𝟙ᵐ ∣ n ] Γ ◂ p ·ᶜ γ +ᶜ δ                               →⟨ subsumption-®∷[∣]◂ (λ _ → proj₂ ∘→ +ᶜ-positive-⟨⟩ (_ ·ᶜ γ)) ⟩

         σ ® σ′ ∷[ 𝟙ᵐ ∣ n ] Γ ◂ δ                                         →⟨ ▸⊩ʳ∷⇔ .proj₁ ⊩ʳu ⊢σ ⟩

         u [ σ ] ® erase str u T.[ σ′ ] ∷ A [ starʷ l ]₀ [ σ ] ◂ 𝟙        →⟨ conv-®∷◂ $
                                                                             PE.subst₂ (_⊢_≡_ _) (PE.sym $ singleSubstLift A _)
                                                                               (PE.sym $ singleSubstLift A _) $
                                                                             substTypeEq (refl ⊢A[σ⇑]) (sym′ t[σ]≡⋆) ⟩

         u [ σ ] ® erase str u T.[ σ′ ] ∷ A [ t ]₀ [ σ ] ◂ 𝟙              →⟨ ®∷◂-⇐* unitrec⇛u[σ] unitrec⇒u[σ′] ⟩

         unitrec l p q A t u [ σ ] ®
           erase str (unitrec l p q A t u) T.[ σ′ ] ∷ A [ t ]₀ [ σ ] ◂ 𝟙  □)
    of λ
      unitrec® →

    case PE.subst (_⊢_∷_ _ _) (singleSubstLift A _) $
         subst-⊢∷-⇑ ⊢u ⊢σ of λ
      ⊢u[σ] →
    case subst-⊢∷ ⊢t ⊢σ of λ
      ⊢t[σ] →
    case inversion-Unit (syntacticTerm ⊢t) of λ
      ok →
    case Unitʷ-η? of λ where
      (yes η) →
        unitrec® (η-unit ⊢t[σ] (starⱼ ⊢Δ ok) (inj₂ η))
          (                          ∷ A [ t ]₀ [ σ ]           ⟨ singleSubstLift A _ ⟩⇛≡
           unitrec l p q A t u [ σ ] ∷ A [ σ ⇑ ] [ t [ σ ] ]₀  ⇒⟨ unitrec-β-η ⊢A[σ⇑] ⊢t[σ] ⊢u[σ] ok
                                                                    (Unit-with-η-𝕨→Unitʷ-η (inj₂ η)) ⟩∎⇛∷
           u [ σ ]                                             ∎)
      (no no-η) →
        case red-Unit ⊢t[σ] of λ where
          (_ , starₙ {s} , t[σ]⇒⋆) →
            case inversion-star-Unit (syntacticRedTerm t[σ]⇒⋆ .proj₂ .proj₂) of λ {
              (PE.refl , PE.refl , _) →
            unitrec® (subset*Term t[σ]⇒⋆)
              (                                  ∷ A [ t ]₀ [ σ ]            ⟨ singleSubstLift A _ ⟩⇛≡
              unitrec l p q A t         u [ σ ] ∷ A [ σ ⇑ ] [ t [ σ ] ]₀  ⇒*⟨ unitrec-subst* t[σ]⇒⋆ ⊢A[σ⇑] ⊢u[σ] no-η ⟩⇛∷
                                                                            ⟨ substTypeEq (refl ⊢A[σ⇑]) (subset*Term t[σ]⇒⋆) ⟩⇛
              unitrec l p q A (starʷ l) u [ σ ] ∷ A [ σ ⇑ ] [ starʷ l ]₀  ⇒⟨ unitrec-β ⊢A[σ⇑] ⊢u[σ] ok no-η ⟩∎⇛∷
              u [ σ ]                                                     ∎)}
          (t′ , ne t′-ne , t[σ]⇒t′) →
            ⊥-elim $
            case is-𝟘? p of λ where
              (no p≢𝟘) →
                case p≢𝟘→t[σ]®t[σ′] p≢𝟘 of λ {
                  (starᵣ t[σ]⇛⋆ _) →
                starʷ≢ne no-η idᶠ t′-ne
                  (starʷ l  ≡˘⟨ ⇛→⊢≡ t[σ]⇛⋆ ⟩⊢
                   t [ σ ]  ⇒*⟨ t[σ]⇒t′ ⟩⊢∎
                   t′       ∎) }
              (yes p≡𝟘) → case p≡𝟘→ p≡𝟘 of λ where
                (inj₂ η)        → no-η η
                (inj₁ (ε , tr)) →
                  glass-closed-no-ne $
                  PE.subst (flip (Neutral _) _) tr t′-ne
