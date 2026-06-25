------------------------------------------------------------------------
-- Some admissible rules related to Id
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Properties.Admissible.Identity.Primitive
  {ℓ} {M : Set ℓ}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Modality 𝕄
open Type-restrictions R

open import Definition.Untyped M
import Definition.Untyped.Erased 𝕄 as Erased
open import Definition.Untyped.Properties M

open import Definition.Typed R
open import Definition.Typed.Inversion.Primitive R
open import Definition.Typed.Properties.Admissible.Equality R
open import Definition.Typed.Properties.Admissible.Var R
open import Definition.Typed.Weakening R
open import Definition.Typed.Well-formed R

open import Tools.Fin
open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE

private variable
  Γ                    : Cons _ _
  A B eq eq₁ eq₂ t u v w : Term _
  l                    : Lvl _
  s                    : Strength
  p q : M

------------------------------------------------------------------------
-- Variants of some typing rules

opaque

  -- A variant of Idⱼ.

  Idⱼ′ : Γ ⊢ t ∷ A → Γ ⊢ u ∷ A → Γ ⊢ Id A t u
  Idⱼ′ ⊢t = Idⱼ (wf-⊢ ⊢t) ⊢t

opaque

  -- A variant of the typing rule for rfl.

  rflⱼ′ :
    Γ ⊢ t ≡ u ∷ A →
    Γ ⊢ rfl ∷ Id A t u
  rflⱼ′ t≡u =
    let ⊢A , ⊢t , _ = wf-⊢ t≡u in
    conv (rflⱼ ⊢t) (Id-cong (refl ⊢A) (refl ⊢t) t≡u)

opaque

  -- A variant of the typing rule for J.

  Jⱼ′ :
    Γ »∙ A »∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
    Γ ⊢ u ∷ B [ t , rfl ]₁₀ →
    Γ ⊢ w ∷ Id A t v →
    Γ ⊢ J p q A t B u v w ∷ B [ v , w ]₁₀
  Jⱼ′ ⊢B ⊢u ⊢w =
    let _ , ⊢t , ⊢v = inversion-Id (wf-⊢ ⊢w) in
    Jⱼ ⊢t ⊢B ⊢u ⊢v ⊢w

opaque

  -- A variant of []-congⱼ.

  []-congⱼ′ :
    let open Erased s in
    []-cong-allowed s →
    Γ ⊢ l ∷Level →
    Γ ⊢ v ∷ Id A t u →
    Γ ⊢ []-cong s l A t u v ∷ Id (Erased l A) ([ t ]) ([ u ])
  []-congⱼ′ ok ⊢l ⊢v =
    let ⊢A , ⊢t , ⊢u = inversion-Id (wf-⊢ ⊢v) in
    []-congⱼ ⊢l ⊢A ⊢t ⊢u ⊢v ok

------------------------------------------------------------------------
-- Lemmas related to equality reflection

opaque

  -- A variant of equality-reflection.

  equality-reflection′ :
    Equality-reflection →
    Γ ⊢ v ∷ Id A t u →
    Γ ⊢ t ≡ u ∷ A
  equality-reflection′ ok ⊢v =
    equality-reflection ok (wf-⊢ ⊢v) ⊢v

opaque

  -- In the presence of equality reflection one can prove a
  -- definitional variant of UIP.

  uip-with-equality-reflection-≡ :
    Equality-reflection →
    Γ ⊢ eq₁ ∷ Id A t u →
    Γ ⊢ eq₂ ∷ Id A t u →
    Γ ⊢ eq₁ ≡ eq₂ ∷ Id A t u
  uip-with-equality-reflection-≡ ok ⊢eq₁ ⊢eq₂ =
    trans (lemma ⊢eq₁) (sym′ (lemma ⊢eq₂))
    where
    lemma : Γ ⊢ eq ∷ Id A t u → Γ ⊢ eq ≡ rfl ∷ Id A t u
    lemma ⊢eq =
      let ⊢A , ⊢t , _ = inversion-Id (wf-⊢ ⊢eq)
          ⊢Id         = var₀ $ Idⱼ′ (wk₁ ⊢A ⊢t) (var₀ ⊢A)
      in
      equality-reflection′ ok $
      PE.subst (_⊢_∷_ _ _)
        (PE.cong₃ Id
           (PE.cong₃ Id wk2-[,] wk2-[,] PE.refl) PE.refl PE.refl) $
      Jⱼ′ {p = ω} {q = ω}
        (Idⱼ′ ⊢Id (rflⱼ′ (equality-reflection′ ok ⊢Id)))
        (rflⱼ $
         PE.subst (_⊢_∷_ _ _)
           (PE.sym $ PE.cong₃ Id wk2-[,] wk2-[,] PE.refl) $
         rflⱼ ⊢t)
        ⊢eq
opaque

  -- In the presence of equality reflection every identity proof is
  -- judgementally equal to rfl.

  ⊢≡rfl∷Id :
    Equality-reflection →
    Γ ⊢ eq ∷ Id A t u →
    Γ ⊢ eq ≡ rfl ∷ Id A t u
  ⊢≡rfl∷Id ok ⊢eq =
    uip-with-equality-reflection-≡ ok ⊢eq
      (rflⱼ′ (equality-reflection′ ok ⊢eq))

opaque

  -- In the presence of equality reflection one can prove a variant of
  -- UIP.

  uip-with-equality-reflection-Id :
    Equality-reflection →
    Γ ⊢ eq₁ ∷ Id A t u →
    Γ ⊢ eq₂ ∷ Id A t u →
    Γ ⊢ rfl ∷ Id (Id A t u) eq₁ eq₂
  uip-with-equality-reflection-Id ok ⊢eq₁ ⊢eq₂ =
    rflⱼ′ (uip-with-equality-reflection-≡ ok ⊢eq₁ ⊢eq₂)
