------------------------------------------------------------------------
-- Some lemmas used in Graded.Has-box-cong.Equivalent,
-- Graded.Has-box-cong.Equivalent.For-level and
-- Graded.Has-box-cong.Definable
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
import Graded.Modality
open import Graded.Mode.Instances.Zero-one.Variant
open import Graded.Usage.Restrictions

module Graded.Has-box-cong.Lemmas
  {a} {M : Set a}
  (open Graded.Modality M)
  {𝕄 : Modality}
  (TR : Type-restrictions 𝕄)
  (variant : Mode-variant 𝕄)
  where

open Modality 𝕄
open Type-restrictions TR

open import Definition.Typed TR
open import Definition.Typed.Properties TR
open import Definition.Untyped M

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Mode.Instances.Zero-one variant

open import Tools.Fin
open import Tools.Nat using (Nat)

private variable
  n   : Nat
  Γ   : Cons _ _
  l   : Lvl _
  p q : M

opaque

  -- A lemma related to Id.

  ⊢Id-2-1-0′ :
    Γ ⊢ l ∷Level →
    Γ »∙ U l »∙ var x0 »∙ var x1 ⊢ Id (var x2) (var x1) (var x0)
  ⊢Id-2-1-0′ {Γ} {l} ⊢l = Idⱼ′ (var₁ ⊢1) (var₀ ⊢1)
    where
    ⊢1 : Γ »∙ U l »∙ var x0 ⊢ var x1
    ⊢1 = univ (var₁ (univ (var₀ (⊢U ⊢l))))

opaque

  -- A lemma related to Id.

  ⊢Id-2-1-0 :
    Level-allowed →
    ⊢ Γ →
    Γ »∙ Level »∙ U (level (var x0)) »∙ var x0 »∙ var x1 ⊢
      Id (var x2) (var x1) (var x0)
  ⊢Id-2-1-0 ok ⊢Γ = ⊢Id-2-1-0′ (term-⊢∷ (var₀ (Levelⱼ′ ok ⊢Γ)))

opaque

  -- A lemma related to _,_≔_.

  ·ᶜ𝟘ᶜ,≔ :
    (x : Fin n) →
    p ·ᶜ (𝟘ᶜ , x ≔ q) ≈ᶜ 𝟘ᶜ , x ≔ p · q
  ·ᶜ𝟘ᶜ,≔ {p} {q} x = begin
    p ·ᶜ (𝟘ᶜ , x ≔ q)    ≡˘⟨ update-distrib-·ᶜ _ _ _ _ ⟩
    p ·ᶜ 𝟘ᶜ , x ≔ p · q  ≈⟨ update-congˡ (·ᶜ-zeroʳ _) ⟩
    𝟘ᶜ , x ≔ p · q       ∎
    where
    open ≈ᶜ-reasoning

opaque

  -- A lemma related to _,_≔_.

  ·ᶜ𝟘ᶜ,≔⌜ᵐ·⌝ :
    ∀ m (x : Fin n) →
    p ·ᶜ (𝟘ᶜ , x ≔ ⌜ m ᵐ· p ⌝) ≈ᶜ 𝟘ᶜ , x ≔ ⌜ m ⌝ · p
  ·ᶜ𝟘ᶜ,≔⌜ᵐ·⌝ {p} m x = begin
    p ·ᶜ (𝟘ᶜ , x ≔ ⌜ m ᵐ· p ⌝)  ≈⟨ ·ᶜ𝟘ᶜ,≔ _ ⟩
    𝟘ᶜ , x ≔ p · ⌜ m ᵐ· p ⌝     ≈⟨ update-congʳ (·⌜ᵐ·⌝ m) ⟩
    𝟘ᶜ , x ≔ p · ⌜ m ⌝          ≈˘⟨ update-congʳ (⌜⌝-·-comm m) ⟩
    𝟘ᶜ , x ≔ ⌜ m ⌝ · p          ∎
    where
    open ≈ᶜ-reasoning
