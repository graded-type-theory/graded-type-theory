------------------------------------------------------------------------
-- Validity for Lift
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Erasure.LogicalRelation.Assumptions
open import Graded.Modality

module Graded.Erasure.LogicalRelation.Fundamental.Lift
  {a} {M : Set a}
  {𝕄 : Modality M}
  (open Modality 𝕄)
  {R : Type-restrictions 𝕄}
  (as : Assumptions R)
  ⦃ 𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet ⦄
  where

open Assumptions as

open import Definition.LogicalRelation.Substitution R
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Substitution R
open import Definition.Untyped M

open import Graded.Context 𝕄
open import Graded.Erasure.Extraction 𝕄
open import Graded.Erasure.LogicalRelation as
open import Graded.Erasure.LogicalRelation.Hidden as
import Graded.Erasure.Target as T
open import Graded.Modality.Properties 𝕄
open import Graded.Mode 𝕄

open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE

private variable
  Γ     : Con Term _
  A t u : Term _
  γ     : Conₘ _
  m     : Mode

opaque

  -- Validity for Lift.

  Liftʳ :
    Γ ⊢ u ∷Level →
    γ ▸ Γ ⊩ʳ Lift t A ∷[ m ] U u
  Liftʳ ⊢u =
    ▸⊩ʳ∷⇔ .proj₂ λ ⊩σ _ →
    ®∷→®∷◂ $
    ®∷U⇔ .proj₂
      ( subst-⊢∷L ⊢u (escape-⊩ˢ∷ ⊩σ .proj₂)
      , U/Levelᵣ (λ { PE.refl → T.refl })
      )

opaque

  -- Validity for lift.

  liftʳ :
    Γ ⊢ t ∷Level →
    Γ ⊢ u ∷ A →
    γ ▸ Γ ⊩ʳ u ∷[ m ] A →
    γ ▸ Γ ⊩ʳ lift u ∷[ m ] Lift t A
  liftʳ {m = 𝟘ᵐ} _ _ _ =
    ▸⊩ʳ∷[𝟘ᵐ]
  liftʳ {Γ} {t} {u} {A} {γ} {m = 𝟙ᵐ} ⊢t ⊢u ⊩ʳu =
    ▸⊩ʳ∷⇔ .proj₂ λ {σ = σ} {σ′ = σ′} ⊩σ σ®σ′ →
    let _ , ⊢σ = escape-⊩ˢ∷ ⊩σ
        ⊢t[σ]  = subst-⊢∷L ⊢t ⊢σ
    in
    ®∷→®∷◂ $
    ®∷Lift⇔ .proj₂
      ( ⊢t[σ]
      , (                                                         $⟨ σ®σ′ ⟩
         σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ γ                                     →⟨ ®∷→®∷◂ω non-trivial ∘→ ▸⊩ʳ∷⇔ .proj₁ ⊩ʳu ⊩σ ⟩
         u [ σ ] ® erase str u T.[ σ′ ] ∷ A [ σ ]                 →⟨ ®∷-⇐* (⇒*→⇛ (redMany (Lift-β⇒ (subst-⊢∷ ⊢u ⊢σ)))) T.refl ⟩
         lower (lift u) [ σ ] ® erase str u T.[ σ′ ] ∷ A [ σ ]    □)
      )

opaque

  -- Validity for lower.

  lowerʳ :
    γ ▸ Γ ⊩ʳ t ∷[ m ] Lift u A →
    γ ▸ Γ ⊩ʳ lower t ∷[ m ] A
  lowerʳ {m = 𝟘ᵐ} _ =
    ▸⊩ʳ∷[𝟘ᵐ]
  lowerʳ {γ} {Γ} {t} {m = 𝟙ᵐ} {u} {A} ⊩ʳt =
    ▸⊩ʳ∷⇔ .proj₂ λ {σ = σ} {σ′ = σ′} ⊩σ σ®σ′ →
    ®∷→®∷◂ $
    ®∷Lift⇔ .proj₁
      (                                                 $⟨ σ®σ′ ⟩
       σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ γ                             →⟨ ®∷→®∷◂ω non-trivial ∘→ ▸⊩ʳ∷⇔ .proj₁ ⊩ʳt ⊩σ ⟩
       t [ σ ] ® erase str t T.[ σ′ ] ∷ Lift u A [ σ ]  □)
      .proj₂
