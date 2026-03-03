------------------------------------------------------------------------
-- Validity for the identity type
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Erasure.LogicalRelation.Assumptions
open import Graded.Modality
open import Graded.Mode.Instances.Zero-one.Variant

module Graded.Erasure.LogicalRelation.Fundamental.Identity
  {a} {M : Set a}
  {𝕄 : Modality M}
  (open Modality 𝕄)
  {R : Type-restrictions 𝕄}
  (variant : Mode-variant 𝕄)
  (as : Assumptions R)
  ⦃ 𝟘-well-behaved : Has-well-behaved-zero M 𝕄 ⦄
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
open import Definition.Typed.Well-formed R

open import Definition.Untyped M
import Definition.Untyped.Erased 𝕄 as Erased
open import Definition.Untyped.Properties M

open import Graded.Context 𝕄
open import Graded.Context.Properties.Has-well-behaved-zero 𝕄
open import Graded.Erasure.Extraction 𝕄
open import Graded.Erasure.LogicalRelation as
open import Graded.Erasure.LogicalRelation.Assumptions.Reasoning
  is-reduction-relation
open import Graded.Erasure.LogicalRelation.Hidden variant as
import Graded.Erasure.Target as T
open import Graded.Mode.Instances.Zero-one variant

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality as PE using (_≡_)
open import Tools.Sum using (_⊎_; inj₁; inj₂)

private variable
  n             : Nat
  Γ             : Con Term _
  γ δ           : Conₘ _
  A B l t u v w : Term _
  m             : Mode
  p q           : M
  s             : Strength

opaque

  -- Validity of Id.

  Idʳ :
    ts » Γ ⊢ v ∷Level →
    γ ▸ Γ ⊩ʳ Id A t u ∷[ m ∣ n ] U v
  Idʳ ⊢v =
    ▸⊩ʳ∷⇔ .proj₂ λ ⊢σ _ →
    ®∷→®∷◂ $
    ®∷U⇔ .proj₂
      ( subst-⊢∷L ⊢v ⊢σ
      , U/Levelᵣ (λ { PE.refl → T.refl })
      )

opaque

  -- Validity of rfl.

  rflʳ :
    ts » Γ ⊢ t ∷ A →
    γ ▸ Γ ⊩ʳ rfl ∷[ m ∣ n ] Id A t t
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

  -- Validity of []-cong for empty variable contexts and transparent
  -- definition contexts.

  []-congʳ :
    Empty-con Δ × Transparent ts →
    ts » Γ ⊢ l ∷Level →
    ts » Γ ⊢ v ∷ Id A t u →
    []-cong-allowed s →
    let open Erased s in
    γ ▸ Γ ⊩ʳ []-cong s l A t u v ∷[ m ∣ n ]
      Id (Erased l A) [ t ] ([ u ])
  []-congʳ {l} {v} {A} {t} {u} (ε , tr) ⊢l ⊢v ok =
    let ⊢A , _ = inversion-Id (wf-⊢∷ ⊢v) in
    ▸⊩ʳ∷⇔ .proj₂ λ {σ = σ} ⊢σ _ →
    ®∷→®∷◂ $
    ®∷Id⇔ .proj₂
      ( PE.subst (_⊢_ _) (PE.sym $ Erased.Erased-[] _)
          (Erasedⱼ ([]-cong→Erased ok) (subst-⊢∷L ⊢l ⊢σ)
             (subst-⊢ ⊢A ⊢σ))
      , rflᵣ
          (                              ˘⟨ Erased.Id-Erased-[] _ ⟩⇛≡
           ([]-cong _ l A t u v) [ σ ]  ⇒*⟨ PE.subst₄ _⊢_⇒*_∷_
                                              (PE.cong (_» _) (PE.sym tr)) PE.refl PE.refl PE.refl $
                                            ε⊢⇒*rfl∷Id $ []-congⱼ′ ok (subst-⊢∷L ⊢l ⊢σ) (subst-⊢∷ ⊢v ⊢σ) ⟩∎⇛
           rfl                          ∎)
          (λ { PE.refl → T.refl })
      )

opaque

  -- Validity of K.

  Kʳ :
    ts » Γ ∙ Id A t t ⊢ B →
    ts » Γ ⊢ u ∷ B [ rfl ]₀ →
    ts » Γ ⊢ v ∷ Id A t t →
    K-allowed →
    γ ≤ᶜ δ →
    δ ▸ Γ ⊩ʳ u ∷[ m ∣ n ] B [ rfl ]₀ →
    Empty-con Δ × Transparent ts ⊎
    (∃ λ η → γ ≤ᶜ η × η ▸ Γ ⊩ʳ v ∷[ m ∣ n ] Id A t t) →
    γ ▸ Γ ⊩ʳ K p A t B u v ∷[ m ∣ n ] B [ v ]₀
  Kʳ {m = 𝟘ᵐ} _ _ _ _ _ _ _ =
    ▸⊩ʳ∷[𝟘ᵐ]
  Kʳ
    {Γ} {A} {t} {B} {u} {v} {γ} {δ} {m = 𝟙ᵐ} {n} {p}
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
         (inj₁ (ε , tr)) →                           $⟨ ⊢v[σ] ⟩
           ts » ε ⊢ v [ σ ] ∷ Id A t t [ σ ]         →⟨ PE.subst₄ _⊢_⇒*_∷_
                                                          (PE.cong (_» _) (PE.sym tr)) PE.refl PE.refl PE.refl ∘→
                                                        ε⊢⇒*rfl∷Id ⟩
           ts » ε ⊢ v [ σ ] ⇒* rfl ∷ Id A t t [ σ ]  →⟨ ⇒*→⇛ ⟩
           v [ σ ] ⇛ rfl ∷ Id A t t [ σ ]            □
         (inj₂ (η , γ≤η , ⊩ʳv)) →                               $⟨ σ®σ′ ⟩

           σ ® σ′ ∷[ 𝟙ᵐ ∣ n ] Γ ◂ γ                             →⟨ subsumption-®∷[∣]◂ (λ _ → ≤ᶜ→⟨⟩≡𝟘→⟨⟩≡𝟘 γ≤η) ⟩

           σ ® σ′ ∷[ 𝟙ᵐ ∣ n ] Γ ◂ η                             →⟨ ▸⊩ʳ∷⇔ .proj₁ ⊩ʳv ⊢σ ⟩

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
    σ ® σ′ ∷[ 𝟙ᵐ ∣ n ] Γ ◂ γ                                         →⟨ subsumption-®∷[∣]◂ (λ _ → ≤ᶜ→⟨⟩≡𝟘→⟨⟩≡𝟘 γ≤δ) ⟩
    σ ® σ′ ∷[ 𝟙ᵐ ∣ n ] Γ ◂ δ                                         →⟨ ▸⊩ʳ∷⇔ .proj₁ ⊩ʳu ⊢σ ⟩
    u [ σ ] ® erase str u T.[ σ′ ] ∷ B [ rfl ]₀ [ σ ] ◂ 𝟙            →⟨ conv-®∷◂ ⊢B[rfl]≡B[v] ⟩
    u [ σ ] ® erase str u T.[ σ′ ] ∷ B [ v ]₀ [ σ ] ◂ 𝟙              →⟨ ®∷◂-⇐* K⇛u[σ] T.refl ⟩
    K p A t B u v [ σ ] ® erase str u T.[ σ′ ] ∷ B [ v ]₀ [ σ ] ◂ 𝟙  □

opaque

  -- Validity of J.

  Jʳ :
    ts » Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
    ts » Γ ⊢ u ∷ B [ t , rfl ]₁₀ →
    ts » Γ ⊢ w ∷ Id A t v →
    γ ≤ᶜ δ →
    δ ▸ Γ ⊩ʳ u ∷[ m ∣ n ] B [ t , rfl ]₁₀ →
    Empty-con Δ × Transparent ts ⊎
    (∃ λ η → γ ≤ᶜ η × η ▸ Γ ⊩ʳ w ∷[ m ∣ n ] Id A t v) →
    γ ▸ Γ ⊩ʳ J p q A t B u v w ∷[ m ∣ n ] B [ v , w ]₁₀
  Jʳ {m = 𝟘ᵐ} _ _ _ _ _ _ =
    ▸⊩ʳ∷[𝟘ᵐ]
  Jʳ
    {Γ} {A} {t} {B} {u} {w} {v} {γ} {δ} {m = 𝟙ᵐ} {n} {p} {q}
    ⊢B ⊢u ⊢w γ≤δ ⊩ʳu ε⊎⊩ʳw =
    ▸⊩ʳ∷⇔ .proj₂ λ {σ = σ} {σ′ = σ′} ⊢σ σ®σ′ →
    case PE.subst₂ _⊢_ (PE.cong (_»∙_ _) (Id-wk1-wk1-0[⇑]≡ A t))
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
         (inj₁ (ε , tr)) →                           $⟨ ⊢w[σ] ⟩
           ts » ε ⊢ w [ σ ] ∷ Id A t v [ σ ]         →⟨ PE.subst₄ _⊢_⇒*_∷_
                                                          (PE.cong (_» _) (PE.sym tr)) PE.refl PE.refl PE.refl ∘→
                                                        ε⊢⇒*rfl∷Id ⟩
           ts » ε ⊢ w [ σ ] ⇒* rfl ∷ Id A t v [ σ ]  →⟨ ⇒*→⇛ ⟩
           w [ σ ] ⇛ rfl ∷ Id A t v [ σ ]            □
         (inj₂ (η , γ≤η , ⊩ʳw)) →                               $⟨ σ®σ′ ⟩

           σ ® σ′ ∷[ 𝟙ᵐ ∣ n ] Γ ◂ γ                             →⟨ subsumption-®∷[∣]◂ (λ _ → ≤ᶜ→⟨⟩≡𝟘→⟨⟩≡𝟘 γ≤η) ⟩

           σ ® σ′ ∷[ 𝟙ᵐ ∣ n ] Γ ◂ η                             →⟨ ▸⊩ʳ∷⇔ .proj₁ ⊩ʳw ⊢σ ⟩

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

    σ ® σ′ ∷[ 𝟙ᵐ ∣ n ] Γ ◂ γ                                    →⟨ subsumption-®∷[∣]◂ (λ _ → ≤ᶜ→⟨⟩≡𝟘→⟨⟩≡𝟘 γ≤δ) ⟩

    σ ® σ′ ∷[ 𝟙ᵐ ∣ n ] Γ ◂ δ                                    →⟨ ▸⊩ʳ∷⇔ .proj₁ ⊩ʳu ⊢σ ⟩

    u [ σ ] ® erase str u T.[ σ′ ] ∷ B [ t , rfl ]₁₀ [ σ ] ◂ 𝟙  →⟨ conv-®∷◂ ⊢B[t,rfl]≡B[v,w] ⟩

    u [ σ ] ® erase str u T.[ σ′ ] ∷ B [ v , w ]₁₀ [ σ ] ◂ 𝟙    →⟨ ®∷◂-⇐* J⇛u[σ] T.refl ⟩

    J p q A t B u v w [ σ ] ® erase str u T.[ σ′ ] ∷
      B [ v , w ]₁₀ [ σ ] ◂ 𝟙                                   □
