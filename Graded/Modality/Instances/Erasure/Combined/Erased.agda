------------------------------------------------------------------------
-- Admissible combined typing/usage rules for Erased
------------------------------------------------------------------------

open import Tools.Bool using (true; T)
open import Tools.Level

open import Definition.Typed.Restrictions

open import Graded.Modality.Instances.Erasure.Modality
open import Graded.Usage.Restrictions
open import Graded.Mode.Instances.Zero-one.Variant ErasureModality
open import Graded.Mode.Instances.Zero-one 𝟘ᵐ-Allowed

module Graded.Modality.Instances.Erasure.Combined.Erased
  (TR : Type-restrictions ErasureModality)
  (UR : Usage-restrictions ErasureModality Zero-one-isMode)
  where

open Type-restrictions TR
open Usage-restrictions UR

private

  -- The modality used in this module.

  𝕄 : Modality
  𝕄 = ErasureModality

  open module M = Modality 𝕄 using (Trivial)

open import Graded.Context 𝕄
open import Graded.Derived.Erased.Usage UR using (▸Erased; ▸[])
open import Graded.Derived.Erased.Usage.Zero-one UR
open import Graded.Modality.Instances.Erasure
open import Graded.Modality.Instances.Erasure.Combined TR UR
open import Graded.Modality.Instances.Erasure.Combined.Equivalent TR UR
open import Graded.Modality.Instances.Erasure.Properties
open import Graded.Usage UR
open import Graded.Usage.Properties UR

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
  Γ                                                       : Cons _ _
  A A₁ A₂ B B₁ B₂ l l₁ l₂ t t₁ t₂ u u₁ u₂ v v₁ v₂ w w₁ w₂ : Term _
  γ                                                       : Conₘ _
  p q                                                     : Erasure
  s                                                       : Strength

-- The following properties are proven under the asuumption that certain
-- things must always be allowed when the mode is 𝟘ᵐ[ ok ].

module _ (ok-𝟘ᵐ : Allowed-at-𝟘ᵐ) where

  private opaque

    -- A lemma used below.

    ∷U→▸ : γ ▸ Γ ⊢ A ∷[ p ] U l → 𝟘ᶜ ▸[ 𝟘ᵐ? ] l
    ∷U→▸ ⊢A =
      let ⊢l = ⊢∷L←⊢∷L ok-𝟘ᵐ (inversion-U-Level (wf-⊢∷ (⊢∷[]→⊢∷ ⊢A))) in
      ▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) (⊢∷L→▸ ⊢l)

  opaque

    -- A typing/usage rule for Erased.

    ⊢-Erased :
      let open Erased s in
      Erased-allowed s →
      Γ ⊢ l ∷Level →
      Γ ⊢ A →
      γ ▸ Γ ⊢[ p ] Erased l A
    ⊢-Erased ok ⊢l ⊢A =
      ⊢[]←⊢▸ ok-𝟘ᵐ (Erasedⱼ ok (⊢∷L→⊢∷L ⊢l) (⊢[]→⊢ ⊢A))
        (sub
          (▸Erased _ (▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) (⊢∷L→▸ ⊢l))
            (▸-cong ⌞𝟘⌟≡𝟘ᵐ? (⊢[]→▸ ⊢A)))
          (greatest-elemᶜ _))

  opaque


    -- An equality rule for Erased.

    ⊢≡-Erased :
      let open Erased s in
      Erased-allowed s →
      Γ ⊢ l₁ ≡ l₂ ∷Level →
      Γ ⊢ A₁ ≡ A₂ →
      Γ ⊢ Erased l₁ A₁ ≡ Erased l₂ A₂
    ⊢≡-Erased ok l₁≡l₂ A₁≡A₂ =
      ⊢≡←⊢≡ ok-𝟘ᵐ (Erased-cong ok (⊢≡∷L→⊢≡∷L l₁≡l₂) (⊢≡→⊢≡ A₁≡A₂))

  opaque

    -- A typing/usage rule for Erased.

    ⊢∷-Erased :
      let open Erased s in
      Erased-allowed s →
      Γ ⊢ A ∷ U l →
      γ ▸ Γ ⊢ Erased l A ∷[ p ] U l
    ⊢∷-Erased ok ⊢A =
      ⊢∷[]←⊢∷▸ ok-𝟘ᵐ (Erasedⱼ-U ok (⊢∷[]→⊢∷ ⊢A))
        (sub (▸Erased _ (∷U→▸ ⊢A) (▸-cong ⌞𝟘⌟≡𝟘ᵐ? (⊢∷[]→▸ ⊢A)))
          (greatest-elemᶜ _))

  opaque

    -- An equality rule for Erased.

    ⊢≡∷-Erased :
      let open Erased s in
      Erased-allowed s →
      Γ ⊢ l₁ ≡ l₂ ∷Level →
      Γ ⊢ A₁ ≡ A₂ ∷ U l₁ →
      Γ ⊢ Erased l₁ A₁ ≡ Erased l₂ A₂ ∷ U l₁
    ⊢≡∷-Erased ok l₁≡l₂ A₁≡A₂ =
      ⊢≡∷←⊢≡∷ ok-𝟘ᵐ (Erased-cong-U ok (⊢≡∷L→⊢≡∷L l₁≡l₂) (⊢≡∷→⊢≡∷ A₁≡A₂))

  opaque

    -- A typing/usage rule for [_].

    ⊢∷-[] :
      let open Erased s in
      Erased-allowed s →
      Γ ⊢ l ∷Level →
      Γ ⊢ t ∷ A →
      𝟘ᶜ ▸ Γ ⊢ [ t ] ∷[ p ] Erased l A
    ⊢∷-[] ok ⊢l ⊢t =
      ⊢∷[]←⊢∷▸ ok-𝟘ᵐ ([]ⱼ ok (⊢∷L→⊢∷L ⊢l) (⊢∷[]→⊢∷ ⊢t))
        (▸[] _ (▸-cong ⌞𝟘⌟≡𝟘ᵐ? (⊢∷[]→▸ ⊢t)))

  opaque

    -- An equality rule for [_].

    ⊢≡∷-[] :
      let open Erased s in
      Erased-allowed s →
      Γ ⊢ l ∷Level →
      Γ ⊢ t ≡ u ∷ A →
      Γ ⊢ [ t ] ≡ [ u ] ∷ Erased l A
    ⊢≡∷-[] ok ⊢l t≡u =
      ⊢≡∷←⊢≡∷ ok-𝟘ᵐ ([]-cong′ ok (⊢∷L→⊢∷L ⊢l) (⊢≡∷→⊢≡∷ t≡u))

  opaque

    -- A typing/usage rule for erased.

    ⊢∷-erased :
      let open Erased s in
      Γ ⊢ t ∷ Erased l A →
      Γ ⊢ erased A t ∷ A
    ⊢∷-erased ⊢t =
      let ⊢t′ = ⊢∷[]→⊢∷ ⊢t
          ⊢A  = ⊢←⊢ ok-𝟘ᵐ (inversion-Erased (wf-⊢∷ ⊢t′) .proj₂ .proj₁)
      in
      ⊢∷[]←⊢∷▸ ok-𝟘ᵐ (erasedⱼ ⊢t′)
        (▸-cong (PE.sym ⌞𝟘⌟′) $
         ▸erased _ (▸-cong ⌞𝟘⌟′ (⊢∷[]→▸ ⊢t))
           (λ _ → 𝟘ᶜ , ▸-cong ⌞𝟘⌟′ (⊢[]→▸ ⊢A))
           λ _ → Allowed-at-𝟘ᵐ.pr ok-𝟘ᵐ _ _ _)

  opaque

    -- An equality rule for erased.

    ⊢≡∷-erased :
      let open Erased s in
      Γ ⊢ A ≡ B →
      Γ ⊢ t ≡ u ∷ Erased l A →
      Γ ⊢ erased A t ≡ erased B u ∷ A
    ⊢≡∷-erased A≡B t≡u =
      ⊢≡∷←⊢≡∷ ok-𝟘ᵐ (erased-cong (⊢≡→⊢≡ A≡B) (⊢≡∷→⊢≡∷ t≡u))

  opaque

    -- Another equality rule for erased.

    ⊢≡∷-erased-[] :
      let open Erased s in
      Erased-allowed s →
      Γ ⊢ t ∷ A →
      Γ ⊢ erased A [ t ] ≡ t ∷ A
    ⊢≡∷-erased-[] ok = ⊢≡∷←⊢≡∷ ok-𝟘ᵐ ∘→ Erased-β ok ∘→ ⊢∷[]→⊢∷

  opaque

    -- A typing/usage rule for erasedrec.

    ⊢∷-erasedrec :
      let open Erased s in
      (s PE.≡ 𝕨 → Prodrec-allowed ⌞ q ⌟ ω 𝟘 p) →
      (s PE.≡ 𝕨 → Unitrec-allowed ⌞ q ⌟ ω p) →
      Γ »∙ Erased l A ⊢ B →
      γ ∙ 𝟘 ▸ Γ »∙ A ⊢ t ∷[ q ] B [ [ var x0 ] ]↑ →
      γ ▸ Γ ⊢ u ∷[ q · is-𝕨 ] Erased l A →
      γ ▸ Γ ⊢ erasedrec p B t u ∷[ q ] B [ u ]₀
    ⊢∷-erasedrec {p} {γ} ok₁ ok₂ ⊢B ⊢t ⊢u =
      ⊢∷[]←⊢∷▸ ok-𝟘ᵐ (⊢erasedrec (⊢[]→⊢ ⊢B) (⊢∷[]→⊢∷ ⊢t) (⊢∷[]→⊢∷ ⊢u))
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
      Γ »∙ Erased l A ⊢ B₁ ≡ B₂ →
      Γ »∙ A ⊢ t₁ ≡ t₂ ∷ B₁ [ [ var x0 ] ]↑ →
      Γ ⊢ u₁ ≡ u₂ ∷ Erased l A →
      Γ ⊢ erasedrec p B₁ t₁ u₁ ≡ erasedrec p B₂ t₂ u₂ ∷ B₁ [ u₁ ]₀
    ⊢≡∷-erasedrec B₁≡B₂ t₁≡t₂ u₁≡u₂ =
      ⊢≡∷←⊢≡∷ ok-𝟘ᵐ $
      erasedrec-cong (⊢≡→⊢≡ B₁≡B₂) (⊢≡∷→⊢≡∷ t₁≡t₂) (⊢≡∷→⊢≡∷ u₁≡u₂)

  opaque

    -- Another equality rule for erasedrec.

    ⊢≡∷-erasedrec-[] :
      let open Erased s in
      Γ »∙ Erased l A ⊢ B →
      Γ »∙ A ⊢ t ∷ B [ [ var x0 ] ]↑ →
      Γ ⊢ u ∷ A →
      Γ ⊢ erasedrec p B t [ u ] ≡ t [ u ]₀ ∷ B [ [ u ] ]₀
    ⊢≡∷-erasedrec-[] ⊢B ⊢t ⊢u =
      ⊢≡∷←⊢≡∷ ok-𝟘ᵐ $ erasedrec-β (⊢[]→⊢ ⊢B) (⊢∷[]→⊢∷ ⊢t) (⊢∷[]→⊢∷ ⊢u)

  opaque

    -- A typing/usage rule for mapᴱ.

    ⊢∷-mapᴱ :
      let open Erased s in
      Γ ⊢ l₂ ∷Level →
      Γ »∙ A ⊢ t ∷ wk1 B →
      Γ ⊢ u ∷ Erased l₁ A →
      𝟘ᶜ ▸ Γ ⊢ mapᴱ A t u ∷[ p ] Erased l₂ B
    ⊢∷-mapᴱ {s} ⊢l₂ ⊢t ⊢u =
      let ⊢t′ = ⊢∷[]→⊢∷ ⊢t
          ⊢A  = ⊢←⊢ ok-𝟘ᵐ (⊢∙→⊢ (wfTerm ⊢t′))
      in
      ⊢∷[]←⊢∷▸ ok-𝟘ᵐ (⊢mapᴱ (⊢∷L→⊢∷L ⊢l₂) ⊢t′ (⊢∷[]→⊢∷ ⊢u))
        (▸mapᴱ s
          (λ _ → Allowed-at-𝟘ᵐ.pr ok-𝟘ᵐ _ _ _)
          (λ _ → _ , ▸-cong ⌞𝟘⌟′ (⊢[]→▸ ⊢A))
          (▸-cong ⌞𝟘⌟′ (⊢∷[]→▸ ⊢t)) (▸-cong ⌞𝟘⌟′ (⊢∷[]→▸ ⊢u)))

  opaque

    -- An equality rule for mapᴱ.

    ⊢≡∷-mapᴱ :
      let open Erased s in
      Γ ⊢ l₂ ∷Level →
      Γ ⊢ A₁ ≡ A₂ →
      Γ »∙ A₁ ⊢ t₁ ≡ t₂ ∷ wk1 B →
      Γ ⊢ u₁ ≡ u₂ ∷ Erased l₁ A₁ →
      Γ ⊢ mapᴱ A₁ t₁ u₁ ≡ mapᴱ A₂ t₂ u₂ ∷ Erased l₂ B
    ⊢≡∷-mapᴱ ⊢l₂ A₁≡A₂ t₁≡t₂ u₁≡u₂ =
      ⊢≡∷←⊢≡∷ ok-𝟘ᵐ $
      mapᴱ-cong (⊢∷L→⊢∷L ⊢l₂) (⊢≡→⊢≡ A₁≡A₂) (⊢≡∷→⊢≡∷ t₁≡t₂)
        (⊢≡∷→⊢≡∷ u₁≡u₂)

  opaque

    -- Another equality rule for mapᴱ.

    ⊢≡∷-mapᴱ-[] :
      let open Erased s in
      Erased-allowed s →
      Γ ⊢ l ∷Level →
      Γ »∙ A ⊢ t ∷ wk1 B →
      Γ ⊢ u ∷ A →
      Γ ⊢ mapᴱ A t [ u ] ≡ [ t [ u ]₀ ] ∷ Erased l B
    ⊢≡∷-mapᴱ-[] ok ⊢l ⊢t ⊢u =
      ⊢≡∷←⊢≡∷ ok-𝟘ᵐ $ mapᴱ-β ok (⊢∷L→⊢∷L ⊢l) (⊢∷[]→⊢∷ ⊢t) (⊢∷[]→⊢∷ ⊢u)

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
          ⊢A           = ⊢←⊢ ok-𝟘ᵐ ⊢A
          ⊢t           = ⊢∷←⊢∷ ok-𝟘ᵐ ⊢t
          ⊢v           = ⊢∷←⊢∷ ok-𝟘ᵐ ⊢v
      in
      ⊢∷[]←⊢∷▸ ok-𝟘ᵐ (⊢Jᵉ ok₁ (⊢[]→⊢ ⊢B) (⊢∷[]→⊢∷ ⊢u) (⊢∷[]→⊢∷ ⊢w))
        (sub
           (▸Jᵉ _ (λ _ → ⊥-elim ∘→ (_$ _))
              (λ _ → PE.subst (λ m → Prodrec-allowed m ω 𝟘 𝟘)
                        (PE.sym 𝟘ᵐ?≡𝟘ᵐ) (Allowed-at-𝟘ᵐ.pr ok-𝟘ᵐ _ _ _))
              (λ _ → ⊥-elim ∘→ (_$ _)) ok₂
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
      ⊢≡∷←⊢≡∷ ok-𝟘ᵐ $
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
      ⊢≡∷←⊢≡∷ ok-𝟘ᵐ $ Jᵉ-≡ ok (⊢∷[]→⊢∷ ⊢t) (⊢[]→⊢ ⊢B) (⊢∷[]→⊢∷ ⊢u)
