------------------------------------------------------------------------
-- Validity for the identity type
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Erasure.LogicalRelation.Assumptions
open import Graded.Modality

module Graded.Erasure.LogicalRelation.Fundamental.Identity
  {a} {M : Set a}
  {𝕄 : Modality M}
  (open Modality 𝕄)
  {R : Type-restrictions 𝕄}
  (as : Assumptions R)
  ⦃ 𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet ⦄
  where

open Assumptions as
open Has-well-behaved-zero 𝟘-well-behaved
open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Consequences.Canonicity R
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Substitution R
open import Definition.Typed.Syntactic R

open import Definition.Untyped M
import Definition.Untyped.Erased 𝕄 as Erased
open import Definition.Untyped.Properties M

open import Graded.Context 𝕄
open import Graded.Context.Properties.Has-well-behaved-zero 𝕄
open import Graded.Erasure.Extraction 𝕄
open import Graded.Erasure.LogicalRelation as
open import Graded.Erasure.LogicalRelation.Assumptions.Reasoning
  is-reduction-relation
open import Graded.Erasure.LogicalRelation.Hidden as
import Graded.Erasure.Target as T
open import Graded.Mode 𝕄

open import Tools.Fin
open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality as PE using (_≡_)
open import Tools.Sum using (_⊎_; inj₁; inj₂)

private variable
  Γ           : Con Term _
  γ δ         : Conₘ _
  A B t u v w : Term _
  m           : Mode
  p q         : M
  s           : Strength
  l           : Universe-level

opaque

  -- Validity of Id.

  Idʳ : γ ▸ Γ ⊩ʳ Id A t u ∷[ m ] U l
  Idʳ =
    ▸⊩ʳ∷⇔ .proj₂ λ _ _ →
    ®∷→®∷◂ (®∷U⇔ .proj₂ (Uᵣ (λ { PE.refl → T.refl })))

opaque

  -- Validity of rfl.

  rflʳ :
    Γ ⊢ t ∷ A →
    γ ▸ Γ ⊩ʳ rfl ∷[ m ] Id A t t
  rflʳ ⊢t =
    ▸⊩ʳ∷⇔ .proj₂ λ ⊢σ _ →
    let ⊢σt = subst-⊢∷ ⊢t ⊢σ in
    ®∷→®∷◂ $
    ®∷Id⇔ .proj₂
      (syntacticTerm ⊢σt
      , rflᵣ
          (rfl  ∎⟨ rflⱼ ⊢σt ⟩⇛)
          (λ { PE.refl → T.refl }))

opaque

  -- Validity of []-cong for empty "target contexts".

  []-congʳ :
    Empty-con Δ →
    Γ ⊢ v ∷ Id A t u →
    []-cong-allowed s →
    let open Erased s in
    γ ▸ Γ ⊩ʳ []-cong s A t u v ∷[ m ] Id (Erased A) [ t ] ([ u ])
  []-congʳ {v} {A} {t} {u} ε ⊢v ok =
    ▸⊩ʳ∷⇔ .proj₂ λ {σ = σ} ⊢σ _ →
    let ⊢σv = subst-⊢∷ ⊢v ⊢σ
        ⊢σA , _ = inversion-Id (syntacticTerm ⊢σv)
    in
    ®∷→®∷◂ $
    ®∷Id⇔ .proj₂
      ( Erasedⱼ ([]-cong→Erased ok) ⊢σA
      , rflᵣ
          (([]-cong _ A t u v) [ σ ]  ⇒*⟨ ε⊢⇒*rfl∷Id $ []-congⱼ′ ok ⊢σv ⟩∎⇛
           rfl                        ∎)
          (λ { PE.refl → T.refl })
      )

opaque

  -- Validity of K.

  Kʳ :
    Γ ∙ Id A t t ⊢ B →
    Γ ⊢ u ∷ B [ rfl ]₀ →
    Γ ⊢ v ∷ Id A t t →
    K-allowed →
    γ ≤ᶜ δ →
    δ ▸ Γ ⊩ʳ u ∷[ m ] B [ rfl ]₀ →
    Empty-con Δ ⊎ (∃ λ η → γ ≤ᶜ η × η ▸ Γ ⊩ʳ v ∷[ m ] Id A t t) →
    γ ▸ Γ ⊩ʳ K p A t B u v ∷[ m ] B [ v ]₀
  Kʳ {m = 𝟘ᵐ} _ _ _ _ _ _ _ =
    ▸⊩ʳ∷[𝟘ᵐ]
  Kʳ
    {Γ} {A} {t} {B} {u} {v} {γ} {δ} {m = 𝟙ᵐ} {p}
    ⊢B ⊢u ⊢v ok γ≤δ ⊩ʳu ε⊎⊩ʳv =
    ▸⊩ʳ∷⇔ .proj₂ λ {σ = σ} {σ′ = σ′} ⊢σ σ®σ′ →
    case subst-⊢∷ ⊢v ⊢σ of λ
      ⊢v[σ] →
    case subst-⊢-⇑ ⊢B ⊢σ of λ
      ⊢B[σ⇑] →
    case PE.subst (_⊢_∷_ _ _) (singleSubstLift B _) $
         subst-⊢∷ ⊢u ⊢σ of λ
      ⊢u[σ] →
    case
      (case ε⊎⊩ʳv of λ where
         (inj₁ ε) →                             $⟨ ⊢v[σ] ⟩
           ε ⊢ v [ σ ] ∷ Id A t t [ σ ]         →⟨ ε⊢⇒*rfl∷Id ⟩
           ε ⊢ v [ σ ] ⇒* rfl ∷ Id A t t [ σ ]  →⟨ ⇒*→⇛ ⟩
           v [ σ ] ⇛ rfl ∷ Id A t t [ σ ]       □
         (inj₂ (η , γ≤η , ⊩ʳv)) →                               $⟨ σ®σ′ ⟩

           σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ γ                                 →⟨ subsumption-®∷[]◂ (λ _ → ≤ᶜ→⟨⟩≡𝟘→⟨⟩≡𝟘 γ≤η) ⟩

           σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ η                                 →⟨ ▸⊩ʳ∷⇔ .proj₁ ⊩ʳv ⊢σ ⟩

           v [ σ ] ® erase str v T.[ σ′ ] ∷ Id A t t [ σ ] ◂ 𝟙  →⟨ proj₂ ∘→ ®∷Id⇔ .proj₁ ∘→ ®∷→®∷◂ω non-trivial ⟩

           v [ σ ] ® erase str v T.[ σ′ ]
             ∷Id⟨ A [ σ ] ⟩⟨ t [ σ ] ⟩⟨ t [ σ ] ⟩               →⟨ (λ { (rflᵣ v[σ]⇛rfl _) → v[σ]⇛rfl }) ⟩

           v [ σ ] ⇛ rfl ∷ Id A t t [ σ ]                       □)
    of λ
      v[σ]⇛rfl →
    case PE.subst₂ (_⊢_≡_ _) (PE.sym (singleSubstLift B _)) (PE.sym (singleSubstLift B _)) $
         substTypeEq (refl ⊢B[σ⇑]) (sym′ (⇛→⊢≡ v[σ]⇛rfl)) of λ
      ⊢B[rfl]≡B[v] →
    case                  ∷ B [ v ]₀ [ σ ]           ⟨ singleSubstLift B _ ⟩⇛≡
      K p A t B u v [ σ ] ∷ B [ σ ⇑ ] [ v [ σ ] ]₀  ⇛⟨ K-⇛ ⊢B[σ⇑] ⊢u[σ] v[σ]⇛rfl ok ⟩∷
                                                     ⟨ substTypeEq (refl ⊢B[σ⇑]) (⇛→⊢≡ v[σ]⇛rfl) ⟩⇛
      K p A t B u rfl [ σ ] ∷ B [ σ ⇑ ] [ rfl ]₀    ⇒⟨ K-β ⊢B[σ⇑] ⊢u[σ] ok ⟩∎⇛∷
      u [ σ ]                                       ∎
    of λ
      K⇛u[σ] →                                                       $⟨ σ®σ′ ⟩
    σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ γ                                             →⟨ subsumption-®∷[]◂ (λ _ → ≤ᶜ→⟨⟩≡𝟘→⟨⟩≡𝟘 γ≤δ) ⟩
    σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ δ                                             →⟨ ▸⊩ʳ∷⇔ .proj₁ ⊩ʳu ⊢σ ⟩
    u [ σ ] ® erase str u T.[ σ′ ] ∷ B [ rfl ]₀ [ σ ] ◂ 𝟙            →⟨ conv-®∷◂ ⊢B[rfl]≡B[v] ⟩
    u [ σ ] ® erase str u T.[ σ′ ] ∷ B [ v ]₀ [ σ ] ◂ 𝟙              →⟨ ®∷◂-⇐* K⇛u[σ] T.refl ⟩
    K p A t B u v [ σ ] ® erase str u T.[ σ′ ] ∷ B [ v ]₀ [ σ ] ◂ 𝟙  □

opaque

  -- Validity of J.

  Jʳ :
    Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
    Γ ⊢ u ∷ B [ t , rfl ]₁₀ →
    Γ ⊢ w ∷ Id A t v →
    γ ≤ᶜ δ →
    δ ▸ Γ ⊩ʳ u ∷[ m ] B [ t , rfl ]₁₀ →
    Empty-con Δ ⊎ (∃ λ η → γ ≤ᶜ η × η ▸ Γ ⊩ʳ w ∷[ m ] Id A t v) →
    γ ▸ Γ ⊩ʳ J p q A t B u v w ∷[ m ] B [ v , w ]₁₀
  Jʳ {m = 𝟘ᵐ} _ _ _ _ _ _ =
    ▸⊩ʳ∷[𝟘ᵐ]
  Jʳ
    {Γ} {A} {t} {B} {u} {w} {v} {γ} {δ} {m = 𝟙ᵐ} {p} {q}
    ⊢B ⊢u ⊢w γ≤δ ⊩ʳu ε⊎⊩ʳw =
    ▸⊩ʳ∷⇔ .proj₂ λ {σ = σ} {σ′ = σ′} ⊢σ σ®σ′ →
    case PE.subst₂ _⊢_ (PE.cong (_∙_ _) (Id-wk1-wk1-0[⇑]≡ A t))
           PE.refl $
         subst-⊢-⇑ ⊢B ⊢σ of λ
      ⊢B[σ⇑⇑] →
    case PE.subst (_⊢_∷_ _ _) ([,]-[]-commute B) $
         subst-⊢∷ ⊢u ⊢σ of λ
      ⊢u[σ] →
    case subst-⊢∷ ⊢w ⊢σ of λ
      ⊢w[σ] →
    case
      (case ε⊎⊩ʳw of λ where
         (inj₁ ε) →                             $⟨ ⊢w[σ] ⟩
           ε ⊢ w [ σ ] ∷ Id A t v [ σ ]         →⟨ ε⊢⇒*rfl∷Id ⟩
           ε ⊢ w [ σ ] ⇒* rfl ∷ Id A t v [ σ ]  →⟨ ⇒*→⇛ ⟩
           w [ σ ] ⇛ rfl ∷ Id A t v [ σ ]       □
         (inj₂ (η , γ≤η , ⊩ʳw)) →                               $⟨ σ®σ′ ⟩

           σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ γ                                 →⟨ subsumption-®∷[]◂ (λ _ → ≤ᶜ→⟨⟩≡𝟘→⟨⟩≡𝟘 γ≤η) ⟩

           σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ η                                 →⟨ ▸⊩ʳ∷⇔ .proj₁ ⊩ʳw ⊢σ ⟩

           w [ σ ] ® erase str w T.[ σ′ ] ∷ Id A t v [ σ ] ◂ 𝟙  →⟨ proj₂ ∘→ ®∷Id⇔ .proj₁ ∘→ ®∷→®∷◂ω non-trivial ⟩

           w [ σ ] ® erase str w T.[ σ′ ]
             ∷Id⟨ A [ σ ] ⟩⟨ t [ σ ] ⟩⟨ v [ σ ] ⟩               →⟨ (λ { (rflᵣ w[σ]⇛rfl _) → w[σ]⇛rfl }) ⟩

           w [ σ ] ⇛ rfl ∷ Id A t v [ σ ]                       □)
    of λ
      w[σ]⇛rfl →
    case PE.subst (_⊢_≡_∷_ _ _ _) ≡Id-wk1-wk1-0[]₀ $ ⇛→⊢≡ w[σ]⇛rfl of λ
      w[σ]≡rfl →
    case inversion-rfl-Id (wf-⇛ w[σ]⇛rfl .proj₂) of λ
      t[σ]≡v[σ] →
    case PE.subst₂ (_⊢_≡_ _) (PE.sym ([,]-[]-commute B)) (PE.sym ([,]-[]-commute B)) $
          substTypeEq₂ (refl ⊢B[σ⇑⇑]) t[σ]≡v[σ] $
          conv (sym′ w[σ]≡rfl) $
          substTypeEq (refl (⊢∙→⊢ (wf ⊢B[σ⇑⇑]))) (sym′ t[σ]≡v[σ])
            of λ
      ⊢B[t,rfl]≡B[v,w] →
    case                      ∷ B [ v , w ]₁₀ [ σ ]                   ⟨ [,]-[]-commute B ⟩⇛≡
      J p q A t B u v w [ σ ] ∷ B [ σ ⇑ ⇑ ] [ v [ σ ] , w [ σ ] ]₁₀  ⇛⟨ J-⇛ ⊢B[σ⇑⇑] ⊢u[σ] w[σ]⇛rfl ⟩∷
                                                                      ⟨ substTypeEq₂ (refl ⊢B[σ⇑⇑]) (sym′ t[σ]≡v[σ])
                                                                        w[σ]≡rfl ⟩⇛
      J p q A t B u v rfl [ σ ] ∷ B [ σ ⇑ ⇑ ] [ t [ σ ] , rfl ]₁₀    ⇒⟨ J-β-⇒ t[σ]≡v[σ] ⊢B[σ⇑⇑] ⊢u[σ] ⟩∎⇛∷
      u [ σ ]                                                        ∎
    of λ
      J⇛u[σ] →                                                  $⟨ σ®σ′ ⟩

    σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ γ                                        →⟨ subsumption-®∷[]◂ (λ _ → ≤ᶜ→⟨⟩≡𝟘→⟨⟩≡𝟘 γ≤δ) ⟩

    σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ δ                                        →⟨ ▸⊩ʳ∷⇔ .proj₁ ⊩ʳu ⊢σ ⟩

    u [ σ ] ® erase str u T.[ σ′ ] ∷ B [ t , rfl ]₁₀ [ σ ] ◂ 𝟙  →⟨ conv-®∷◂ ⊢B[t,rfl]≡B[v,w] ⟩

    u [ σ ] ® erase str u T.[ σ′ ] ∷ B [ v , w ]₁₀ [ σ ] ◂ 𝟙    →⟨ ®∷◂-⇐* J⇛u[σ] T.refl ⟩

    J p q A t B u v w [ σ ] ® erase str u T.[ σ′ ] ∷
      B [ v , w ]₁₀ [ σ ] ◂ 𝟙                                   □
