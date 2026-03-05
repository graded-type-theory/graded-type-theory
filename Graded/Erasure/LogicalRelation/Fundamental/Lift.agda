------------------------------------------------------------------------
-- Validity for Lift
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Erasure.LogicalRelation.Assumptions
open import Graded.Modality
open import Graded.Mode.Instances.Zero-one.Variant

module Graded.Erasure.LogicalRelation.Fundamental.Lift
  {a} {M : Set a}
  {𝕄 : Modality M}
  (open Modality 𝕄)
  {R : Type-restrictions 𝕄}
  (variant : Mode-variant 𝕄)
  (as : Assumptions R)
  ⦃ 𝟘-well-behaved : Has-well-behaved-zero M 𝕄 ⦄
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
open import Graded.Erasure.LogicalRelation.Hidden variant as
import Graded.Erasure.Target as T
open import Graded.Modality.Properties 𝕄
open import Graded.Mode.Instances.Zero-one variant

open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private variable
  n       : Nat
  Γ       : Con Term _
  A t     : Term _
  l l₁ l₂ : Lvl _
  γ       : Conₘ _
  m       : Mode

opaque

  -- Validity for Lift.

  Liftʳ :
    ts » Γ ⊢ l₁ ∷Level →
    γ ▸ Γ ⊩ʳ Lift l₂ A ∷[ m ∣ n ] U l₁
  Liftʳ ⊢l₁ =
    ▸⊩ʳ∷⇔ .proj₂ λ ⊢σ _ →
    ®∷→®∷◂ $
    ®∷U⇔ .proj₂
      ( subst-⊢∷L ⊢l₁ ⊢σ
      , U/Levelᵣ (λ { PE.refl → T.refl })
      )

opaque

  -- Validity for lift.

  liftʳ :
    ts » Γ ⊢ l ∷Level →
    ts » Γ ⊢ t ∷ A →
    γ ▸ Γ ⊩ʳ t ∷[ m ∣ n ] A →
    γ ▸ Γ ⊩ʳ lift t ∷[ m ∣ n ] Lift l A
  liftʳ {m = 𝟘ᵐ} _ _ _ =
    ▸⊩ʳ∷[𝟘ᵐ]
  liftʳ {Γ} {l} {t} {A} {γ} {m = 𝟙ᵐ} {n} ⊢l ⊢t ⊩ʳt =
    ▸⊩ʳ∷⇔ .proj₂ λ {σ = σ} {σ′ = σ′} ⊢σ σ®σ′ →
    ®∷→®∷◂ $
    ®∷Lift⇔ .proj₂
      ( subst-⊢∷L ⊢l ⊢σ
      , (                                                         $⟨ σ®σ′ ⟩
         σ ® σ′ ∷[ 𝟙ᵐ ∣ n ] Γ ◂ γ                                 →⟨ ®∷→®∷◂ω non-trivial ∘→ ▸⊩ʳ∷⇔ .proj₁ ⊩ʳt ⊢σ ⟩
         t [ σ ] ® erase str t T.[ σ′ ] ∷ A [ σ ]                 →⟨ ®∷-⇐* (⇒*→⇛ (redMany (Lift-β⇒ (subst-⊢∷ ⊢t ⊢σ)))) T.refl ⟩
         lower (lift t) [ σ ] ® erase str t T.[ σ′ ] ∷ A [ σ ]    □)
      )

opaque

  -- Validity for lower.

  lowerʳ :
    γ ▸ Γ ⊩ʳ t ∷[ m ∣ n ] Lift l A →
    γ ▸ Γ ⊩ʳ lower t ∷[ m ∣ n ] A
  lowerʳ {m = 𝟘ᵐ} _ =
    ▸⊩ʳ∷[𝟘ᵐ]
  lowerʳ {γ} {Γ} {t} {m = 𝟙ᵐ} {n} {l} {A} ⊩ʳt =
    ▸⊩ʳ∷⇔ .proj₂ λ {σ = σ} {σ′ = σ′} ⊢σ σ®σ′ →
    ®∷→®∷◂ $
    ®∷Lift⇔ .proj₁
      (                                                 $⟨ σ®σ′ ⟩
       σ ® σ′ ∷[ 𝟙ᵐ ∣ n ] Γ ◂ γ                         →⟨ ®∷→®∷◂ω non-trivial ∘→ ▸⊩ʳ∷⇔ .proj₁ ⊩ʳt ⊢σ ⟩
       t [ σ ] ® erase str t T.[ σ′ ] ∷ Lift l A [ σ ]  □)
      .proj₂
