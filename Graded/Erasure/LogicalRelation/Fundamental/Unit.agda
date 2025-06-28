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
open import Graded.Erasure.LogicalRelation.Assumptions.Reasoning
  is-reduction-relation
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
open import Definition.Typed.Consequences.Inequality R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Reasoning.Term R
open import Definition.Typed.Substitution R
open import Definition.Typed.Well-formed R

open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Fundamental R
open import Definition.LogicalRelation.Fundamental.Reducibility R
open import Definition.LogicalRelation.Hidden R
import Definition.LogicalRelation.Hidden.Restricted R as R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.Introductions R
open import Definition.LogicalRelation.Unary R

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
    A t u v : Term n
    m : Mode
    s : Strength
    p q : M

opaque

  -- Validity of Unit.

  Unitʳ :
    γ ▸ Γ ⊩ʳ Unit s ∷[ m ] U zeroᵘ
  Unitʳ =
    ▸⊩ʳ∷⇔ .proj₂ λ ⊩σ _ →
    ®∷→®∷◂ $
    ®∷U⇔ .proj₂
      ( zeroᵘⱼ ⊢Δ
      , U/Levelᵣ (λ { PE.refl → T.refl })
      )

opaque

  -- Validity of star.

  starʳ :
    Unit-allowed s →
    γ ▸ Γ ⊩ʳ star s ∷[ m ] Unit s
  starʳ ok =
    ▸⊩ʳ∷⇔ .proj₂ λ ⊩σ _ →
    ®∷→®∷◂ $
    ®∷Unit⇔ .proj₂
      (starᵣ (⇒*→⇛ (id (starⱼ ⊢Δ ok))) T.refl)

opaque

  -- Validity of unitrec.

  unitrecʳ :
    Γ ∙ Unitʷ ⊢ A →
    Γ ⊢ u ∷ Unitʷ →
    Γ ⊢ v ∷ A [ starʷ ]₀ →
    γ ▸ Γ ⊩ʳ u ∷[ m ᵐ· p ] Unitʷ →
    δ ▸ Γ ⊩ʳ v ∷[ m ] A [ starʷ ]₀ →
    (p PE.≡ 𝟘 → Empty-con Δ ⊎ Unitʷ-η) →
    p ·ᶜ γ +ᶜ δ ▸ Γ ⊩ʳ unitrec p q A u v ∷[ m ] A [ u ]₀
  unitrecʳ {m = 𝟘ᵐ} _ _ _ _ _ _ =
    ▸⊩ʳ∷[𝟘ᵐ]
  unitrecʳ
    {Γ} {A} {u} {v} {γ} {m = 𝟙ᵐ} {p} {δ} {q}
    ⊢A ⊢u ⊢v ⊩ʳu ⊩ʳv p≡𝟘→ =
    ▸⊩ʳ∷⇔ .proj₂ λ {σ = σ} {σ′ = σ′} ⊩σ σ®σ′ →
    case fundamental-⊩ᵛ ⊢A of λ
      (_ , ⊩A) →
    case fundamental-⊩ᵛ∷ ⊢u of λ
      (_ , ⊩u) →
    case
      (λ p≢𝟘 →
         case PE.sym $ ≢𝟘→⌞⌟≡𝟙ᵐ p≢𝟘 of λ
           𝟙ᵐ≡⌞p⌟ →                                          $⟨ σ®σ′ ⟩

         σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ p ·ᶜ γ +ᶜ δ                      →⟨ (subsumption-®∷[]◂ λ x →

           (p ·ᶜ γ +ᶜ δ) ⟨ x ⟩ PE.≡ 𝟘                        →⟨ proj₁ ∘→ +ᶜ-positive-⟨⟩ (_ ·ᶜ γ) ⟩
           (p ·ᶜ γ) ⟨ x ⟩ PE.≡ 𝟘                             →⟨ ·ᶜ-zero-product-⟨⟩ γ ⟩
           p PE.≡ 𝟘 ⊎ γ ⟨ x ⟩ PE.≡ 𝟘                         →⟨ (λ { (inj₁ p≡𝟘)    → ⊥-elim (p≢𝟘 p≡𝟘)
                                                                   ; (inj₂ γ⟨x⟩≡𝟘) → γ⟨x⟩≡𝟘
                                                                   }) ⟩
           γ ⟨ x ⟩ PE.≡ 𝟘                                    □) ⟩

         σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ γ                                ≡⟨ PE.cong₃ (_®_∷[_]_◂_ _ _) 𝟙ᵐ≡⌞p⌟ PE.refl PE.refl ⟩→

         σ ® σ′ ∷[ ⌞ p ⌟ ] Γ ◂ γ                             →⟨ ▸⊩ʳ∷⇔ .proj₁ ⊩ʳu ⊩σ ⟩

         u [ σ ] ® erase str u T.[ σ′ ] ∷ Unitʷ ◂ ⌜ ⌞ p ⌟ ⌝  →⟨ ®∷→®∷◂ω (non-trivial ∘→ PE.trans (PE.cong ⌜_⌝ 𝟙ᵐ≡⌞p⌟)) ⟩

         u [ σ ] ® erase str u T.[ σ′ ] ∷ Unitʷ              →⟨ ®∷Unit⇔ .proj₁ ⟩

         u [ σ ] ® erase str u T.[ σ′ ] ∷Unit⟨ 𝕨 ⟩           □)
    of λ
      p≢𝟘→u[σ]®u[σ′] →

    case
      (let open Graded.Erasure.Target.Reasoning in
       case is-𝟘? p of λ where
         (yes p≡𝟘) →
           erase str (unitrec p q A u v) T.[ σ′ ]  ≡⟨ PE.cong T._[ _ ] $ unitrec-𝟘 q A p≡𝟘 ⟩⇒
           erase str v T.[ σ′ ]                      ∎⇒
         (no p≢𝟘) →
           case p≢𝟘→u[σ]®u[σ′] p≢𝟘 of λ {
             (starᵣ _ u[σ′]⇒⋆) →
           erase str (unitrec p q A u v) T.[ σ′ ]        ≡⟨ PE.cong T._[ _ ] $ unitrec-ω q A p≢𝟘 ⟩⇒
           T.unitrec (erase str u) (erase str v) T.[ σ′ ]  ⇒*⟨ TP.unitrec-subst* u[σ′]⇒⋆ ⟩
           T.unitrec T.star (erase str v) T.[ σ′ ]         ⇒⟨ T.unitrec-β ⟩
           erase str v T.[ σ′ ]                            ∎⇒ })
    of λ
      unitrec⇒v[σ′] →

    case
      (λ l
         (u[σ]≡⋆ : Δ ⊩⟨ l ⟩ u [ σ ] ≡ starʷ ∷ Unitʷ)
         unitrec⇛v[σ] →                                               $⟨ σ®σ′ ⟩

         σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ p ·ᶜ γ +ᶜ δ                               →⟨ subsumption-®∷[]◂ (λ _ → proj₂ ∘→ +ᶜ-positive-⟨⟩ (_ ·ᶜ γ)) ⟩

         σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ δ                                          →⟨ ▸⊩ʳ∷⇔ .proj₁ ⊩ʳv ⊩σ ⟩

         v [ σ ] ® erase str v T.[ σ′ ] ∷ A [ starʷ ]₀ [ σ ] ◂ 𝟙        →⟨ conv-®∷◂ $ R.⊩≡→ $
                                                                             ⊩ᵛ≡→⊩≡∷→⊩ˢ≡∷→⊩[]₀[]≡[]₀[] (refl-⊩ᵛ≡ ⊩A)
                                                                               (R.→⊩≡∷ $ sym-⊩≡∷ u[σ]≡⋆) (refl-⊩ˢ≡∷ ⊩σ) ⟩

         v [ σ ] ® erase str v T.[ σ′ ] ∷ A [ u ]₀ [ σ ] ◂ 𝟙            →⟨ ®∷◂-⇐* unitrec⇛v[σ] unitrec⇒v[σ′] ⟩

         unitrec p q A u v [ σ ] ®
           erase str (unitrec p q A u v) T.[ σ′ ] ∷ A [ u ]₀ [ σ ] ◂ 𝟙  □)
    of λ
      unitrec® →

    case escape-⊩ˢ∷ ⊩σ of λ
      (_ , ⊢σ) →
    case subst-⊢-⇑ ⊢A ⊢σ of λ
      ⊢A[σ⇑] →
    case R.⊩∷→ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩u ⊩σ of λ
      ⊩u[σ] →
    case PE.subst (_⊢_∷_ _ _) (singleSubstLift A _) $
         subst-⊢∷-⇑ ⊢v ⊢σ of λ
      ⊢v[σ] →
    let ⊩Γ = valid (wfTerm ⊢u)
    in

    case ⊩∷Unit⇔ .proj₁ ⊩u[σ] of λ {
      (ok , Unitₜ u′ (u[σ]⇒u′ , _) prop) →

    case prop of λ where
      (Unitₜˢ η) →
        unitrec® _
          (⊩ᵛ≡∷⇔′ʰ .proj₁
             (η-unitᵛ ⊩u (starᵛ ⊩Γ ok) η)
             .proj₂ .proj₂ ⊩σ)
          (                          ∷ A [ u ]₀ [ σ ]        ⟨ singleSubstLift A _ ⟩⇛≡
           unitrec p q A u v [ σ ] ∷ A [ σ ⇑ ] [ u [ σ ] ]₀  ⇒⟨ unitrec-β-η-⇒ ⊢A[σ⇑] (escape-⊩∷ ⊩u[σ]) ⊢v[σ] (Unit-with-η-𝕨→Unitʷ-η η) ⟩∎⇛∷
           v [ σ ]                                           ∎)

      (Unitₜʷ rest no-η) → case rest of λ where
        starᵣ →
          let u[σ]≡⋆ =
                u [ σ ]          ⇒*⟨ u[σ]⇒u′ ⟩⊢∎
                starʷ  ∎
          in
          unitrec® _ (reducible-⊩≡∷ u[σ]≡⋆ .proj₂)
            (                          ∷ A [ u ]₀ [ σ ]       ⟨ singleSubstLift A _ ⟩⇛≡

             unitrec p q A u v [ σ ] ∷ A [ σ ⇑ ] [ u [ σ ] ]₀ ⇒*⟨ unitrec-subst* u[σ]⇒u′ ⊢A[σ⇑] ⊢v[σ] no-η ⟩⇛∷
                                                                         ⟨ substTypeEq (refl ⊢A[σ⇑]) u[σ]≡⋆ ⟩⇛
             unitrec p q (A [ σ ⇑ ]) starʷ (v [ σ ]) ∷
               A [ σ ⇑ ] [ starʷ ]₀                           ⇒⟨ unitrec-β-⇒ ⊢A[σ⇑] ⊢v[σ] ⟩∎⇛∷

             v [ σ ]                                          ∎)

        (ne (neNfₜ _ u′-ne _)) →
          ⊥-elim $
          case is-𝟘? p of λ where
            (no p≢𝟘) →
              case p≢𝟘→u[σ]®u[σ′] p≢𝟘 of λ {
                (starᵣ u[σ]⇛⋆ _) →
              starʷ≢ne no-η u′-ne
                (starʷ ∷ Unitʷ        ≡˘⟨ ⇛→⊢≡ u[σ]⇛⋆ ⟩⊢∷
                 u [ σ ] ∷ Unitʷ  ⇒*⟨ u[σ]⇒u′ ⟩⊢∷∎
                 u′                         ∎) }
            (yes p≡𝟘) → case p≡𝟘→ p≡𝟘 of λ where
              (inj₁ ε) → noClosedNe u′-ne
              (inj₂ η) → no-η η }
