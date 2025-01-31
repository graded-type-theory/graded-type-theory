------------------------------------------------------------------------
-- Graded.Erasure validity of the unit type.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Erasure.LogicalRelation.Assumptions
open import Graded.Modality

module Graded.Erasure.LogicalRelation.Fundamental.Unit
  {a} {M : Set a}
  {𝕄 : Modality M}
  (open Modality 𝕄)
  {R : Type-restrictions 𝕄}
  (as : Assumptions R)
  ⦃ 𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet ⦄
  where

open Assumptions as
open Type-restrictions R

open import Graded.Modality.Properties.Has-well-behaved-zero
  semiring-with-meet

open import Graded.Erasure.LogicalRelation as
open import Graded.Erasure.LogicalRelation.Hidden as

open import Graded.Erasure.Extraction 𝕄
open import Graded.Erasure.Extraction.Properties 𝕄

import Graded.Erasure.Target as T
import Graded.Erasure.Target.Properties as TP
import Graded.Erasure.Target.Reasoning

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M

open import Definition.Typed R
open import Definition.Typed.Properties R
import Definition.Typed.Reasoning.Reduction R as RR
open import Definition.Typed.Substitution R

open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Fundamental R
open import Definition.LogicalRelation.Hidden R
import Definition.LogicalRelation.Hidden.Restricted R as R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.Introductions.Unit R

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Mode 𝕄


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

  Unitʳ : γ ▸ Γ ⊩ʳ Unit s l ∷[ m ] U l
  Unitʳ =
    ▸⊩ʳ∷⇔ .proj₂ λ _ _ →
    ®∷→®∷◂ (®∷U⇔ .proj₂ (_ , ≤ᵘ-refl , Uᵣ (λ { PE.refl → T.refl })))

opaque

  -- Validity of star.

  starʳ :
    Unit-allowed s →
    γ ▸ Γ ⊩ʳ star s l ∷[ m ] Unit s l
  starʳ ok =
    ▸⊩ʳ∷⇔ .proj₂ λ _ _ →
    ®∷→®∷◂ (®∷Unit⇔ .proj₂ (starᵣ (id (starⱼ ⊢Δ ok)) T.refl))

opaque

  -- Validity of unitrec.

  unitrecʳ :
    Γ ∙ Unitʷ l ⊢ A →
    Γ ⊢ t ∷ Unitʷ l →
    Γ ⊢ u ∷ A [ starʷ l ]₀ →
    γ ▸ Γ ⊩ʳ t ∷[ m ᵐ· p ] Unitʷ l →
    δ ▸ Γ ⊩ʳ u ∷[ m ] A [ starʷ l ]₀ →
    (p PE.≡ 𝟘 → Empty-con Δ ⊎ Unitʷ-η) →
    p ·ᶜ γ +ᶜ δ ▸ Γ ⊩ʳ unitrec l p q A t u ∷[ m ] A [ t ]₀
  unitrecʳ {m = 𝟘ᵐ} _ _ _ _ _ _ =
    ▸⊩ʳ∷[𝟘ᵐ]
  unitrecʳ
    {Γ} {l} {A} {t} {u} {γ} {m = 𝟙ᵐ} {p} {δ} {q}
    ⊢A ⊢t ⊢u ⊩ʳt ⊩ʳu p≡𝟘→ =
    ▸⊩ʳ∷⇔ .proj₂ λ {σ = σ} {σ′ = σ′} ⊩σ σ®σ′ →
    case fundamental-⊩ᵛ ⊢A of λ
      (_ , ⊩A) →
    case fundamental-⊩ᵛ∷ ⊢t of λ
      (_ , ⊩t) →
    case
      (λ p≢𝟘 →
         case PE.sym $ ≢𝟘→⌞⌟≡𝟙ᵐ p≢𝟘 of λ
           𝟙ᵐ≡⌞p⌟ →                                            $⟨ σ®σ′ ⟩

         σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ p ·ᶜ γ +ᶜ δ                        →⟨ (subsumption-®∷[]◂ λ x →

           (p ·ᶜ γ +ᶜ δ) ⟨ x ⟩ PE.≡ 𝟘                                →⟨ proj₁ ∘→ +ᶜ-positive-⟨⟩ (_ ·ᶜ γ) ⟩
           (p ·ᶜ γ) ⟨ x ⟩ PE.≡ 𝟘                                     →⟨ ·ᶜ-zero-product-⟨⟩ γ ⟩
           p PE.≡ 𝟘 ⊎ γ ⟨ x ⟩ PE.≡ 𝟘                                 →⟨ (λ { (inj₁ p≡𝟘)    → ⊥-elim (p≢𝟘 p≡𝟘)
                                                                           ; (inj₂ γ⟨x⟩≡𝟘) → γ⟨x⟩≡𝟘
                                                                           }) ⟩
           γ ⟨ x ⟩ PE.≡ 𝟘                                            □) ⟩

         σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ γ                                  ≡⟨ PE.cong₃ (_®_∷[_]_◂_ _ _) 𝟙ᵐ≡⌞p⌟ PE.refl PE.refl ⟩→

         σ ® σ′ ∷[ ⌞ p ⌟ ] Γ ◂ γ                               →⟨ ▸⊩ʳ∷⇔ .proj₁ ⊩ʳt ⊩σ ⟩

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

    case
      (λ l′
         (t[σ]≡⋆ : Δ ⊩⟨ l′ ⟩ t [ σ ] ≡ starʷ l ∷ Unitʷ l)
         unitrec⇒u[σ] →                                                   $⟨ σ®σ′ ⟩

         σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ p ·ᶜ γ +ᶜ δ                                   →⟨ subsumption-®∷[]◂ (λ _ → proj₂ ∘→ +ᶜ-positive-⟨⟩ (_ ·ᶜ γ)) ⟩

         σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ δ                                             →⟨ ▸⊩ʳ∷⇔ .proj₁ ⊩ʳu ⊩σ ⟩

         u [ σ ] ® erase str u T.[ σ′ ] ∷ A [ starʷ l ]₀ [ σ ] ◂ 𝟙        →⟨ conv-®∷◂ $ R.⊩≡→ $
                                                                             ⊩ᵛ≡→⊩≡∷→⊩ˢ≡∷→⊩[]₀[]≡[]₀[] (refl-⊩ᵛ≡ ⊩A)
                                                                               (R.→⊩≡∷ $ sym-⊩≡∷ t[σ]≡⋆) (refl-⊩ˢ≡∷ ⊩σ) ⟩

         u [ σ ] ® erase str u T.[ σ′ ] ∷ A [ t ]₀ [ σ ] ◂ 𝟙              →⟨ ®∷◂-⇐* unitrec⇒u[σ] unitrec⇒u[σ′] ⟩

         unitrec l p q A t u [ σ ] ®
           erase str (unitrec l p q A t u) T.[ σ′ ] ∷ A [ t ]₀ [ σ ] ◂ 𝟙  □)
    of λ
      unitrec® →

    case escape-⊩ˢ∷ ⊩σ of λ
      (_ , ⊢σ) →
    case subst-⊢-⇑ ⊢A ⊢σ of λ
      ⊢A[σ⇑] →
    case R.⊩∷→ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩t ⊩σ of λ
      ⊩t[σ] →
    case PE.subst (_⊢_∷_ _ _) (singleSubstLift A _) $
         subst-⊢∷-⇑ ⊢u ⊢σ of λ
      ⊢u[σ] →

    case ⊩∷Unit⇔ .proj₁ ⊩t[σ] of λ {
      (_ , ok , Unitₜ _ t[σ]⇒t′ _ rest) →

    let open RR in
    case Unit-with-η? 𝕨 of λ where
      (inj₁ (inj₁ ()))
      (inj₁ (inj₂ η)) →
        unitrec® _
          (⊩ᵛ≡∷⇔′ʰ .proj₁
             (η-unitᵛ ⊩t (starᵛ (wf-⊩ᵛ (wf-⊩ᵛ∷ ⊩t)) ok) (inj₂ η))
             .proj₂ .proj₂ ⊩σ)
          (                          ∷ A [ t ]₀ [ σ ]           ⟨ singleSubstLift A _ ⟩⇒≡
           unitrec l p q A t u [ σ ] ∷ A [ σ ⇑ ] [ t [ σ ] ]₀  ⇒⟨ unitrec-β-η ⊢A[σ⇑] (escape-⊩∷ ⊩t[σ]) ⊢u[σ] ok η ⟩∎∷
           u [ σ ]                                             ∎)

      (inj₂ (_ , no-η)) → case rest of λ where
        starᵣ →
          unitrec® _ (⊩∷-⇐* t[σ]⇒t′ (⊩star ⊢Δ ok))
            (                                  ∷ A [ t ]₀ [ σ ]            ⟨ singleSubstLift A _ ⟩⇒≡
             unitrec l p q A t         u [ σ ] ∷ A [ σ ⇑ ] [ t [ σ ] ]₀  ⇒*⟨ unitrec-subst* t[σ]⇒t′ ⊢A[σ⇑] ⊢u[σ] no-η ⟩∷
                                                                           ⟨ substTypeEq (refl ⊢A[σ⇑]) (subset*Term t[σ]⇒t′) ⟩⇒
             unitrec l p q A (starʷ l) u [ σ ] ∷ A [ σ ⇑ ] [ starʷ l ]₀  ⇒⟨ unitrec-β ⊢A[σ⇑] ⊢u[σ] ok no-η ⟩∎∷
             u [ σ ]                                                     ∎)

        (ne (neNfₜ _ t′-ne _)) →
          ⊥-elim $
          case is-𝟘? p of λ where
            (no p≢𝟘) →
              case p≢𝟘→t[σ]®t[σ′] p≢𝟘 of λ {
                (starᵣ t[σ]⇒⋆ _) →
              star≢ne t′-ne $
              whrDet*Term (t[σ]⇒⋆ , starₙ) (t[σ]⇒t′ , ne t′-ne) }
            (yes p≡𝟘) → case p≡𝟘→ p≡𝟘 of λ where
              (inj₁ ε) → noClosedNe t′-ne
              (inj₂ η) → no-η η }
