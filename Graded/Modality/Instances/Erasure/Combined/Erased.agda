------------------------------------------------------------------------
-- Admissible combined typing/usage rules for Erased
------------------------------------------------------------------------

open import Tools.Bool using (true; T)
open import Tools.Level

open import Definition.Typed.Restrictions

open import Graded.Modality.Variant lzero
open import Graded.Modality.Instances.Erasure.Modality
open import Graded.Usage.Restrictions

module Graded.Modality.Instances.Erasure.Combined.Erased
  (TR : Type-restrictions (ErasureModality (𝟘ᵐ-allowed-if true)))
  (UR : Usage-restrictions (ErasureModality (𝟘ᵐ-allowed-if true)))
  where

open Type-restrictions TR
open Usage-restrictions UR

private

  -- The modality variant used in this module.

  variant : Modality-variant
  variant = 𝟘ᵐ-allowed-if true

private

  -- The modality used in this module.

  𝕄 : Modality
  𝕄 = ErasureModality variant

  open module M = Modality 𝕄 using (Trivial)

open import Graded.Context 𝕄
open import Graded.Derived.Erased.Usage 𝕄 UR
open import Graded.Modality.Instances.Erasure
open import Graded.Modality.Instances.Erasure.Combined TR UR
open import Graded.Modality.Instances.Erasure.Combined.Equivalent TR UR
open import Graded.Modality.Instances.Erasure.Properties variant
open import Graded.Mode 𝕄
open import Graded.Usage 𝕄 UR
open import Graded.Usage.Properties 𝕄 UR

open import Definition.Typed.Inversion TR
open import Definition.Typed.Properties TR
open import Definition.Typed.Well-formed TR
open import Definition.Untyped Erasure hiding (_[_])
import Definition.Untyped.Erased 𝕄 as Erased

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE

private variable
  Γ                                               : Cons _ _
  A A₁ A₂ B B₁ B₂ t t₁ t₂ u u₁ u₂ v v₁ v₂ w w₁ w₂ : Term _
  γ                                               : Conₘ _
  p q                                             : Erasure
  s                                               : Strength
  l                                               : Universe-level

opaque

  -- A typing/usage rule for Erased.

  ⊢-Erased :
    let open Erased s in
    Erased-allowed s →
    Γ ⊢ A →
    γ ▸ Γ ⊢[ p ] Erased A
  ⊢-Erased ok ⊢A =
    ⊢[]←⊢▸ (Erasedⱼ ok (⊢[]→⊢ ⊢A))
      (▸Erased _ (▸-cong ⌞𝟘⌟≡𝟘ᵐ? (sub (⊢[]→▸ ⊢A) (greatest-elemᶜ _))))

opaque

  -- An equality rule for Erased.

  ⊢≡-Erased :
    let open Erased s in
    Erased-allowed s →
    Γ ⊢ A ≡ B →
    Γ ⊢ Erased A ≡ Erased B
  ⊢≡-Erased ok =
    ⊢≡←⊢≡ ∘→ Erased-cong ok ∘→ ⊢≡→⊢≡

opaque

  -- A typing/usage rule for Erased.

  ⊢∷-Erased :
    let open Erased s in
    Erased-allowed s →
    Γ ⊢ A ∷ U l →
    γ ▸ Γ ⊢ Erased A ∷[ p ] U l
  ⊢∷-Erased ok ⊢A =
    ⊢∷[]←⊢∷▸ (Erasedⱼ-U ok (⊢∷[]→⊢∷ ⊢A))
      (▸Erased _ (▸-cong ⌞𝟘⌟≡𝟘ᵐ? (sub (⊢∷[]→▸ ⊢A) (greatest-elemᶜ _))))

opaque

  -- An equality rule for Erased.

  ⊢≡∷-Erased :
    let open Erased s in
    Erased-allowed s →
    Γ ⊢ A ≡ B ∷ U l →
    Γ ⊢ Erased A ≡ Erased B ∷ U l
  ⊢≡∷-Erased ok =
    ⊢≡∷←⊢≡∷ ∘→ Erased-cong-U ok ∘→ ⊢≡∷→⊢≡∷

opaque

  -- A typing/usage rule for [_].

  ⊢∷-[] :
    let open Erased s in
    Erased-allowed s →
    Γ ⊢ t ∷ A →
    𝟘ᶜ ▸ Γ ⊢ [ t ] ∷[ p ] Erased A
  ⊢∷-[] ok ⊢t =
    ⊢∷[]←⊢∷▸ ([]ⱼ ok (⊢∷[]→⊢∷ ⊢t))
      (▸[] _ (▸-cong ⌞𝟘⌟≡𝟘ᵐ? (⊢∷[]→▸ ⊢t)))

opaque

  -- An equality rule for [_].

  ⊢≡∷-[] :
    let open Erased s in
    Erased-allowed s →
    Γ ⊢ t ≡ u ∷ A →
    Γ ⊢ [ t ] ≡ [ u ] ∷ Erased A
  ⊢≡∷-[] ok =
    ⊢≡∷←⊢≡∷ ∘→ []-cong′ ok ∘→ ⊢≡∷→⊢≡∷

opaque

  -- A typing/usage rule for erased.

  ⊢∷-erased :
    let open Erased s in
    Γ ⊢ t ∷ Erased A →
    Γ ⊢ erased A t ∷ A
  ⊢∷-erased ⊢t =
    let ⊢t′ = ⊢∷[]→⊢∷ ⊢t
        ⊢A  = ⊢←⊢ (inversion-Erased (wf-⊢∷ ⊢t′) .proj₁)
    in
    ⊢∷[]←⊢∷▸ (erasedⱼ ⊢t′)
      (▸-cong (PE.sym ⌞𝟘⌟) $
       ▸erased _ (▸-cong ⌞𝟘⌟ (⊢∷[]→▸ ⊢t))
         (λ _ → 𝟘ᶜ , ▸-cong ⌞𝟘⌟ (⊢[]→▸ ⊢A)))

opaque

  -- An equality rule for erased.

  ⊢≡∷-erased :
    let open Erased s in
    Γ ⊢ A ≡ B →
    Γ ⊢ t ≡ u ∷ Erased A →
    Γ ⊢ erased A t ≡ erased B u ∷ A
  ⊢≡∷-erased A≡B t≡u =
    ⊢≡∷←⊢≡∷ (erased-cong (⊢≡→⊢≡ A≡B) (⊢≡∷→⊢≡∷ t≡u))

opaque

  -- Another equality rule for erased.

  ⊢≡∷-erased-[] :
    let open Erased s in
    Erased-allowed s →
    Γ ⊢ t ∷ A →
    Γ ⊢ erased A [ t ] ≡ t ∷ A
  ⊢≡∷-erased-[] ok = ⊢≡∷←⊢≡∷ ∘→ Erased-β ok ∘→ ⊢∷[]→⊢∷

opaque

  -- A typing/usage rule for erasedrec.

  ⊢∷-erasedrec :
    let open Erased s in
    (s PE.≡ 𝕨 → Prodrec-allowed ⌞ q ⌟ ω 𝟘 p) →
    (s PE.≡ 𝕨 → Unitrec-allowed ⌞ q ⌟ ω p) →
    Γ »∙ Erased A ⊢ B →
    γ ∙ 𝟘 ▸ Γ »∙ A ⊢ t ∷[ q ] B [ [ var x0 ] ]↑ →
    γ ▸ Γ ⊢ u ∷[ q · is-𝕨 ] Erased A →
    γ ▸ Γ ⊢ erasedrec p B t u ∷[ q ] B [ u ]₀
  ⊢∷-erasedrec {p} {γ} ok₁ ok₂ ⊢B ⊢t ⊢u =
    ⊢∷[]←⊢∷▸ (⊢erasedrec (⊢[]→⊢ ⊢B) (⊢∷[]→⊢∷ ⊢t) (⊢∷[]→⊢∷ ⊢u))
      (sub
         (▸erasedrec _ (λ _ → ⊥-elim ∘→ (_$ _)) ok₁ ok₂
            (λ _ →
               𝟘ᶜ ,
               (sub (▸-cong ⌞𝟘⌟≡𝟘ᵐ? (⊢[]→▸ ⊢B)) $ begin
                  𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · p  ≈⟨ ≈ᶜ-refl ∙ M.·-congʳ (⌜𝟘ᵐ?⌝≡𝟘 _) ⟩
                  𝟘ᶜ ∙ 𝟘 · p        ≡⟨⟩
                  𝟘ᶜ                ∎))
            (⊢∷[]→▸ ⊢t) (▸-cong (PE.sym ⌞⌟ᵐ·) (⊢∷[]→▸ ⊢u)))
         (begin
            γ       ≡˘⟨ +ᶜ-idem _ ⟩
            γ +ᶜ γ  ∎))
    where
    open ≤ᶜ-reasoning

opaque

  -- An equality rule for erasedrec.

  ⊢≡∷-erasedrec :
    let open Erased s in
    Γ »∙ Erased A ⊢ B₁ ≡ B₂ →
    Γ »∙ A ⊢ t₁ ≡ t₂ ∷ B₁ [ [ var x0 ] ]↑ →
    Γ ⊢ u₁ ≡ u₂ ∷ Erased A →
    Γ ⊢ erasedrec p B₁ t₁ u₁ ≡ erasedrec p B₂ t₂ u₂ ∷ B₁ [ u₁ ]₀
  ⊢≡∷-erasedrec B₁≡B₂ t₁≡t₂ u₁≡u₂ =
    ⊢≡∷←⊢≡∷ $
    erasedrec-cong (⊢≡→⊢≡ B₁≡B₂) (⊢≡∷→⊢≡∷ t₁≡t₂) (⊢≡∷→⊢≡∷ u₁≡u₂)

opaque

  -- Another equality rule for erasedrec.

  ⊢≡∷-erasedrec-[] :
    let open Erased s in
    Γ »∙ Erased A ⊢ B →
    Γ »∙ A ⊢ t ∷ B [ [ var x0 ] ]↑ →
    Γ ⊢ u ∷ A →
    Γ ⊢ erasedrec p B t [ u ] ≡ t [ u ]₀ ∷ B [ [ u ] ]₀
  ⊢≡∷-erasedrec-[] ⊢B ⊢t ⊢u =
    ⊢≡∷←⊢≡∷ $ erasedrec-β (⊢[]→⊢ ⊢B) (⊢∷[]→⊢∷ ⊢t) (⊢∷[]→⊢∷ ⊢u)

opaque

  -- A typing/usage rule for mapᴱ.

  ⊢∷-mapᴱ :
    let open Erased s in
    Γ »∙ A ⊢ t ∷ wk1 B →
    Γ ⊢ u ∷ Erased A →
    𝟘ᶜ ▸ Γ ⊢ mapᴱ A t u ∷[ p ] Erased B
  ⊢∷-mapᴱ {s} ⊢t ⊢u =
    let ⊢u′ = ⊢∷[]→⊢∷ ⊢u
        ⊢A  = ⊢←⊢ (inversion-Erased (wf-⊢∷ ⊢u′) .proj₁)
    in
    ⊢∷[]←⊢∷▸ (⊢mapᴱ (⊢∷[]→⊢∷ ⊢t) ⊢u′)
      (▸mapᴱ s (λ _ → _ , ▸-cong ⌞𝟘⌟ (⊢[]→▸ ⊢A))
         (▸-cong ⌞𝟘⌟ (⊢∷[]→▸ ⊢t)) (▸-cong ⌞𝟘⌟ (⊢∷[]→▸ ⊢u)))

opaque

  -- An equality rule for mapᴱ.

  ⊢≡∷-mapᴱ :
    let open Erased s in
    Γ ⊢ A₁ ≡ A₂ →
    Γ »∙ A₁ ⊢ t₁ ≡ t₂ ∷ wk1 B →
    Γ ⊢ u₁ ≡ u₂ ∷ Erased A₁ →
    Γ ⊢ mapᴱ A₁ t₁ u₁ ≡ mapᴱ A₂ t₂ u₂ ∷ Erased B
  ⊢≡∷-mapᴱ A₁≡A₂ t₁≡t₂ u₁≡u₂ =
    ⊢≡∷←⊢≡∷ $ mapᴱ-cong (⊢≡→⊢≡ A₁≡A₂) (⊢≡∷→⊢≡∷ t₁≡t₂) (⊢≡∷→⊢≡∷ u₁≡u₂)

opaque

  -- Another equality rule for mapᴱ.

  ⊢≡∷-mapᴱ-[] :
    let open Erased s in
    Erased-allowed s →
    Γ »∙ A ⊢ t ∷ wk1 B →
    Γ ⊢ u ∷ A →
    Γ ⊢ mapᴱ A t [ u ] ≡ [ t [ u ]₀ ] ∷ Erased B
  ⊢≡∷-mapᴱ-[] ok ⊢t ⊢u = ⊢≡∷←⊢≡∷ $ mapᴱ-β ok (⊢∷[]→⊢∷ ⊢t) (⊢∷[]→⊢∷ ⊢u)

opaque

  -- A typing/usage rule for Jᵉ.

  ⊢∷-Jᵉ :
    let open Erased s in
    []-cong-allowed s →
    []-cong-allowed-mode s ⌞ p ⌟ →
    γ ∙ 𝟘 ∙ 𝟘 ▸ Γ »∙ A »∙ Id (wk1 A) (wk1 t) (var x0) ⊢[ p ] B →
    γ ▸ Γ ⊢ u ∷[ p ] B [ t , rfl ]₁₀ →
    Γ ⊢ w ∷ Id A t v →
    γ ▸ Γ ⊢ Jᵉ A t B u v w ∷[ p ] B [ v , w ]₁₀
  ⊢∷-Jᵉ {γ} ok₁ ok₂ ⊢B ⊢u ⊢w =
    let ⊢w′          = ⊢∷[]→⊢∷ ⊢w
        ⊢A , ⊢t , ⊢v = inversion-Id (wf-⊢∷ ⊢w′)
        ⊢A           = ⊢←⊢ ⊢A
        ⊢t           = ⊢∷←⊢∷ ⊢t
        ⊢v           = ⊢∷←⊢∷ ⊢v
    in
    ⊢∷[]←⊢∷▸ (⊢Jᵉ ok₁ (⊢[]→⊢ ⊢B) (⊢∷[]→⊢∷ ⊢u) (⊢∷[]→⊢∷ ⊢w))
      (sub
         (▸Jᵉ _ (λ _ → ⊥-elim ∘→ (_$ _)) (λ _ → ⊥-elim ∘→ (_$ _)) ok₂
            (▸-cong ⌞𝟘⌟≡𝟘ᵐ? (⊢[]→▸ ⊢A)) (▸-cong ⌞𝟘⌟≡𝟘ᵐ? (⊢∷[]→▸ ⊢t))
            (⊢[]→▸ ⊢B) (⊢∷[]→▸ ⊢u) (▸-cong ⌞𝟘⌟≡𝟘ᵐ? (⊢∷[]→▸ ⊢v))
            (▸-cong ⌞𝟘⌟≡𝟘ᵐ? (⊢∷[]→▸ ⊢w)))
         (begin
            γ              ≡˘⟨ +ᶜ-idem _ ⟩
            γ +ᶜ γ         ≈˘⟨ ·ᶜ-identityˡ _ ⟩
            ω ·ᶜ (γ +ᶜ γ)  ∎))
    where
    open ≤ᶜ-reasoning

opaque

  -- An equality rule for Jᵉ.

  ⊢≡∷-Jᵉ :
    let open Erased s in
    []-cong-allowed s →
    Γ ⊢ A₁ ≡ A₂ →
    Γ ⊢ t₁ ≡ t₂ ∷ A₁ →
    Γ »∙ A₁ »∙ Id (wk1 A₁) (wk1 t₁) (var x0) ⊢ B₁ ≡ B₂ →
    Γ ⊢ u₁ ≡ u₂ ∷ B₁ [ t₁ , rfl ]₁₀ →
    Γ ⊢ v₁ ≡ v₂ ∷ A₁ →
    Γ ⊢ w₁ ≡ w₂ ∷ Id A₁ t₁ v₁ →
    Γ ⊢ Jᵉ A₁ t₁ B₁ u₁ v₁ w₁ ≡ Jᵉ A₂ t₂ B₂ u₂ v₂ w₂ ∷ B₁ [ v₁ , w₁ ]₁₀
  ⊢≡∷-Jᵉ ok A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ w₁≡w₂ =
    ⊢≡∷←⊢≡∷ $
    Jᵉ-cong ok (⊢≡→⊢≡ A₁≡A₂) (⊢≡∷→⊢≡∷ t₁≡t₂) (⊢≡→⊢≡ B₁≡B₂)
      (⊢≡∷→⊢≡∷ u₁≡u₂) (⊢≡∷→⊢≡∷ v₁≡v₂) (⊢≡∷→⊢≡∷ w₁≡w₂)

opaque

  -- Another equality rule for Jᵉ.

  ⊢≡∷-Jᵉ-rfl :
    let open Erased s in
    []-cong-allowed s →
    Γ ⊢ t ∷ A →
    Γ »∙ A »∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
    Γ ⊢ u ∷ B [ t , rfl ]₁₀ →
    Γ ⊢ Jᵉ A t B u t rfl ≡ u ∷ B [ t , rfl ]₁₀
  ⊢≡∷-Jᵉ-rfl ok ⊢t ⊢B ⊢u =
    ⊢≡∷←⊢≡∷ $ Jᵉ-≡ ok (⊢∷[]→⊢∷ ⊢t) (⊢[]→⊢ ⊢B) (⊢∷[]→⊢∷ ⊢u)
