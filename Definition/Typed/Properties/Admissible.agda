------------------------------------------------------------------------
-- Some admissible typing and equality rules
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Properties.Admissible
  {ℓ} {M : Set ℓ}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped M

open import Definition.Typed R
open import Definition.Typed.Inversion.Primitive R
open import Definition.Typed.Well-formed R

import Graded.Derived.Erased.Untyped 𝕄 as Erased

open import Tools.Fin
open import Tools.Product

open import Definition.Typed.Properties.Admissible.Primitive R public

private variable
  Γ         : Con Term _
  A B t u v : Term _
  s         : Strength
  p q       : M

opaque

  -- A variant of Idⱼ.

  Idⱼ′ : Γ ⊢ t ∷ A → Γ ⊢ u ∷ A → Γ ⊢ Id A t u
  Idⱼ′ ⊢t = Idⱼ (wf-⊢∷ ⊢t) ⊢t

opaque

  -- A variant of lamⱼ.

  lamⱼ′ :
    Π-allowed p q →
    Γ ∙ A ⊢ t ∷ B →
    Γ ⊢ lam p t ∷ Π p , q ▷ A ▹ B
  lamⱼ′ ok ⊢t = lamⱼ (wf-⊢∷ ⊢t) ⊢t ok

opaque

  -- A variant of []-congⱼ.

  []-congⱼ′ :
    let open Erased s in
    []-cong-allowed s →
    Γ ⊢ v ∷ Id A t u →
    Γ ⊢ []-cong s A t u v ∷ Id (Erased A) ([ t ]) ([ u ])
  []-congⱼ′ ok ⊢v =
    let _ , (⊢t , _) , (⊢u , _) = inversion-Id-⊢ (wf-⊢∷ ⊢v) in
    []-congⱼ (wf-⊢∷ ⊢t) ⊢t ⊢u ⊢v ok

opaque

  -- A variant of sym.

  sym′ : Γ ⊢ t ≡ u ∷ A → Γ ⊢ u ≡ t ∷ A
  sym′ t≡u = sym (wf-⊢≡∷ t≡u .proj₁) t≡u

opaque

  -- A variant of η-eq.

  η-eq′ :
    Γ ⊢ t ∷ Π p , q ▷ A ▹ B →
    Γ ⊢ u ∷ Π p , q ▷ A ▹ B →
    Γ ∙ A ⊢ wk1 t ∘⟨ p ⟩ var x0 ≡ wk1 u ∘⟨ p ⟩ var x0 ∷ B →
    Γ ⊢ t ≡ u ∷ Π p , q ▷ A ▹ B
  η-eq′ ⊢t ⊢u t0≡u0 =
    let _ , ⊢B , ok = inversion-ΠΣ (wf-⊢∷ ⊢t) in
    η-eq ⊢B ⊢t ⊢u t0≡u0 ok

opaque

  -- A variant of Σ-η.

  Σ-η′ :
    Γ ⊢ t ∷ Σˢ p , q ▷ A ▹ B →
    Γ ⊢ u ∷ Σˢ p , q ▷ A ▹ B →
    Γ ⊢ fst p t ≡ fst p u ∷ A →
    Γ ⊢ snd p t ≡ snd p u ∷ B [ fst p t ]₀ →
    Γ ⊢ t ≡ u ∷ Σˢ p , q ▷ A ▹ B
  Σ-η′ ⊢t ⊢u t₁≡u₁ t₂≡u₂ =
    let _ , ⊢B , ok = inversion-ΠΣ (wf-⊢∷ ⊢t) in
    Σ-η ⊢B ⊢t ⊢u t₁≡u₁ t₂≡u₂ ok
