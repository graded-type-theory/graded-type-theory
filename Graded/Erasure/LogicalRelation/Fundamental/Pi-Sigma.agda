------------------------------------------------------------------------
-- Validity for Π- and Σ-types
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Erasure.LogicalRelation.Assumptions
open import Graded.Modality
open import Graded.Usage.Restrictions

module Graded.Erasure.LogicalRelation.Fundamental.Pi-Sigma
  {a} {M : Set a}
  {𝕄 : Modality M}
  (open Modality 𝕄)
  {TR : Type-restrictions 𝕄}
  (UR : Usage-restrictions 𝕄)
  (as : Assumptions TR)
  ⦃ 𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet ⦄
  where

open Assumptions as
open Type-restrictions TR

open import Definition.LogicalRelation TR
open import Definition.LogicalRelation.Fundamental TR
open import Definition.LogicalRelation.Fundamental.Reducibility TR
open import Definition.LogicalRelation.Hidden TR
open import Definition.LogicalRelation.Properties TR
import Definition.LogicalRelation.Substitution.Introductions TR as I

open import Definition.Typed TR
open import Definition.Typed.Consequences.DerivedRules TR
open import Definition.Typed.Consequences.Inversion TR
open import Definition.Typed.Consequences.Reduction TR
open import Definition.Typed.Consequences.RedSteps TR
open import Definition.Typed.Consequences.Substitution TR
open import Definition.Typed.Consequences.Syntactic TR
open import Definition.Typed.Properties TR
import Definition.Typed.Reasoning.Reduction TR as RR

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄

open import Graded.Erasure.Extraction 𝕄
open import Graded.Erasure.Extraction.Properties 𝕄
open import Graded.Erasure.LogicalRelation as
open import Graded.Erasure.LogicalRelation.Hidden as
open import Graded.Erasure.LogicalRelation.Value as
import Graded.Erasure.Target as T
open import Graded.Erasure.Target.Non-terminating
import Graded.Erasure.Target.Properties as TP
import Graded.Erasure.Target.Reasoning

open import Graded.Modality.Properties 𝕄

open import Graded.Mode 𝕄

open import Graded.Usage 𝕄 UR
open import Graded.Usage.Inversion 𝕄 UR

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum using (_⊎_; inj₁; inj₂)

private variable
  n         : Nat
  Γ         : Con Term _
  σ         : Subst _ _
  σ′        : T.Subst _ _
  A B C t u : Term _
  γ δ       : Conₘ _
  p q q′ r  : M
  m         : Mode
  b         : BinderMode
  s         : Strength
  l l′ l″   : TypeLevel

------------------------------------------------------------------------
-- A lemma related to Π and Σ

opaque

  -- Validity of Π and Σ.

  ΠΣʳ :
    ⊢ Γ →
    γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ∷[ m ] U
  ΠΣʳ ⊢Γ =
    ▸⊩ʳ∷⇔ .proj₂
      ( I.⊩ᵛU (valid ⊢Γ)
      , λ _ →
          ®∷→®∷◂ (®∷U⇔ .proj₂ ((_ , 0<1) , Uᵣ (λ { PE.refl → T.refl })))
      )

------------------------------------------------------------------------
-- Lemmas related to Π

opaque

  -- Validity of lam.

  lamʳ :
    Π-allowed p q →
    Γ ⊩ᵛ⟨ l ⟩ A →
    Γ ∙ A ⊩ᵛ⟨ l ⟩ t ∷ B →
    γ ∙ ⌜ m ⌝ · p ▸ Γ ∙ A ⊩ʳ⟨ l′ ⟩ t ∷[ m ] B →
    γ ▸ Γ ⊩ʳ⟨ l ⟩ lam p t ∷[ m ] Π p , q ▷ A ▹ B
  lamʳ {p} {Γ} {l} {A} {t} {B} {γ} {m} {l′} ok ⊩A ⊩t ⊩ʳt =
    case wf-⊩ᵛ∷ ⊩t of λ
      ⊩B →
    case I.ΠΣᵛ ok ⊩A ⊩B of λ
      ⊩ΠAB →
    case PE.singleton m of λ {
      (𝟘ᵐ , PE.refl) → ▸⊩ʳ∷[𝟘ᵐ] ⊩ΠAB;
      (𝟙ᵐ , PE.refl) →
    ▸⊩ʳ∷⇔ .proj₂
      ( ⊩ΠAB
      , λ {σ = σ} {σ′ = σ′} σ®σ′ →
          case escape-®∷[]◂ σ®σ′ of λ
            ⊩σ →
          case ⊩ᵛ→⊩ˢ∷→⊩[] ⊩ΠAB ⊩σ of λ
            ⊩ΠAB[σ] →

          ®∷→®∷◂ $
          ®∷Π⇔ .proj₂
            ( ⊩ΠAB[σ]
            , (λ { PE.refl → _ , T.refl })
            , λ t′ ⊢t′ →
                case reducible-⊩∷ ⊢t′ of λ
                  ⊩t′ →
                case ⊩ᵛ→⊩ˢ∷→⊩∷→⊩[,] ⊩B ⊩σ ⊩t′ of λ
                  ⊩B[σ,t′] →
                case redMany $
                     β-red-⇒ (escape-⊩∷ (⊩ᵛ∷→⊩ˢ∷→⊩[⇑]∷ ⊩t ⊩σ)) ⊢t′
                       ok of λ
                  lam-t[σ]∘t′⇒* →

                  (λ { p≡𝟘@PE.refl →
                       case (case PE.singleton str of λ where
                         (T.non-strict , PE.refl) →
                           erase str (lam 𝟘 t) T.[ σ′ ]               ≡⟨ PE.cong T._[ _ ] lam-𝟘-remove ⟩⇒

                           erase str t T.[ loop? str ]₀ T.[ σ′ ]      ≡⟨ TP.singleSubstLift (erase _ t) _ ⟩⇒

                           erase str t T.[ σ′ T.⇑ ]
                             T.[ loop? str T.[ σ′ ] ]₀                ≡⟨ PE.cong (T._[_]₀ (erase _ t T.[ _ ])) $ loop?-[] _ ⟩⇒

                           erase str t T.[ σ′ T.⇑ ] T.[ loop? str ]₀  ∎⇒
                         (T.strict , PE.refl) →
                           (erase str (lam 𝟘 t) T.[ σ′ ]) T.∘⟨ str ⟩
                             loop? str                                ≡⟨ PE.cong₃ T._∘⟨_⟩_ (PE.cong₂ T._[_] (lam-𝟘-keep t) PE.refl)
                                                                           PE.refl PE.refl ⟩⇒
                           (T.lam (erase str t) T.[ σ′ ]) T.∘⟨ str ⟩
                             loop? str                                ⇒⟨ T.β-red T.↯ ⟩

                           erase str t T.[ σ′ T.⇑ ] T.[ loop? str ]₀  ∎⇒)
                       of λ
                         (lam-⌜t⌝[σ′]∘₀⇒* :
                          app-𝟘 str (erase str (lam 𝟘 t) T.[ σ′ ]) T.⇒*
                          erase str t T.[ σ′ T.⇑ ] T.[ loop? str ]₀) →   $⟨ ®∷◂𝟘 (PE.trans (·-identityˡ _) (·-identityˡ _))
                                                                              (⊩ᵛ→⊩ˢ∷→⊩[] ⊩A ⊩σ) ⟩

                       t′ ®⟨ l ⟩ loop? str ∷ A [ σ ] ◂ 𝟙 · 𝟙 · 𝟘         →⟨ (λ t′®loop? →
                                                                               ®∷[]∙◂∙⇔′ .proj₂ ((_ , ⊩A) , (_ , ⊩t′) , (_ , t′®loop?) , σ®σ′)) ⟩
                       consSubst σ t′ ®
                         T.consSubst σ′ (loop? str) ∷[ 𝟙ᵐ ] Γ ∙ A ◂
                         γ ∙ 𝟙 · 𝟘                                       →⟨ ▸⊩ʳ∷⇔ .proj₁ ⊩ʳt .proj₂ ⟩

                       t [ consSubst σ t′ ] ®⟨ l′ ⟩
                         erase str t T.[ T.consSubst σ′ (loop? str) ] ∷
                         B [ consSubst σ t′ ] ◂ 𝟙                        →⟨ level-®∷ ⊩B[σ,t′] ∘→
                                                                            ®∷→®∷◂ω non-trivial ⟩
                       t [ consSubst σ t′ ] ®⟨ l ⟩
                         erase str t T.[ T.consSubst σ′ (loop? str) ] ∷
                         B [ consSubst σ t′ ]                            ≡⟨ PE.cong₄ _®⟨_⟩_∷_ (PE.sym $ singleSubstComp _ _ t) PE.refl
                                                                              (PE.sym $ TP.singleSubstComp _ _ (erase _ t))
                                                                              (PE.sym $ singleSubstComp _ _ B) ⟩→
                       t [ σ ⇑ ] [ t′ ]₀ ®⟨ l ⟩
                         erase str t T.[ σ′ T.⇑ ] T.[ loop? str ]₀ ∷
                         B [ σ ⇑ ] [ t′ ]₀                               →⟨ ®∷-⇐* lam-t[σ]∘t′⇒* lam-⌜t⌝[σ′]∘₀⇒* ⟩

                       (lam 𝟘 t [ σ ]) ∘⟨ 𝟘 ⟩ t′ ®⟨ l ⟩
                         app-𝟘 str (erase str (lam 𝟘 t) T.[ σ′ ]) ∷
                         B [ σ ⇑ ] [ t′ ]₀                               □ })

                , (λ p≢𝟘 v′ t′®v′ →
                     case (case PE.singleton str of λ where
                       (T.non-strict , PE.refl) →
                           v′
                         , T.refl
                         , ((T.lam (erase str t) T.[ σ′ ]) T.∘⟨ str ⟩ v′  ⇒⟨ T.β-red _ ⟩
                            erase str t T.[ T.liftSubst σ′ ] T.[ v′ ]₀    ∎⇒)
                       (T.strict , PE.refl) →
                         case reduces-to-value PE.refl t′®v′ of λ
                           (v″ , v″-value , v′⇒*v″) →
                           v″
                         , v′⇒*v″
                         , ((T.lam (erase str t) T.[ σ′ ]) T.∘⟨ str ⟩ v′  ⇒*⟨ TP.app-subst*-arg T.lam v′⇒*v″ ⟩
                            (T.lam (erase str t) T.[ σ′ ]) T.∘⟨ str ⟩ v″  ⇒⟨ T.β-red v″-value ⟩
                            erase str t T.[ T.liftSubst σ′ ] T.[ v″ ]₀    ∎⇒))
                     of λ
                       ((v″ , v′⇒*v″ , lam-⌜t⌝[σ′]∘v′⇒*) :
                        ∃ λ v″ → v′ T.⇒* v″ ×
                        (T.lam (erase str t) T.[ σ′ ]) T.∘⟨ str ⟩ v′
                          T.⇒*
                        erase str t T.[ T.liftSubst σ′ ] T.[ v″ ]₀) →
                                                                         $⟨ t′®v′ ⟩

                     (t′ ®⟨ l ⟩ v′ ∷ A [ σ ])                            →⟨ ®∷-⇒* v′⇒*v″ ⟩

                     (t′ ®⟨ l ⟩ v″ ∷ A [ σ ])                            →⟨ (λ t′®v″ →
                                                                               ®∷[]∙◂∙⇔′ .proj₂
                                                                                 ((_ , ⊩A) , (_ , ⊩t′) , (_ , ®∷→®∷◂ t′®v″) , σ®σ′)) ⟩
                     consSubst σ t′ ® T.consSubst σ′ v″ ∷[ 𝟙ᵐ ] Γ ∙ A ◂
                       γ ∙ 𝟙 · p                                         →⟨ ▸⊩ʳ∷⇔ .proj₁ ⊩ʳt .proj₂ ⟩

                     t [ consSubst σ t′ ] ®⟨ l′ ⟩
                       erase str t T.[ T.consSubst σ′ v″ ] ∷
                       B [ consSubst σ t′ ] ◂ 𝟙                          →⟨ level-®∷ ⊩B[σ,t′] ∘→
                                                                            ®∷→®∷◂ω non-trivial ⟩
                     t [ consSubst σ t′ ] ®⟨ l ⟩
                       erase str t T.[ T.consSubst σ′ v″ ] ∷
                       B [ consSubst σ t′ ]                              ≡⟨ PE.cong₄ _®⟨_⟩_∷_ (PE.sym $ singleSubstComp _ _ t) PE.refl
                                                                              (PE.sym $ TP.singleSubstComp _ _ (erase _ t))
                                                                              (PE.sym $ singleSubstComp _ _ B) ⟩→
                     t [ σ ⇑ ] [ t′ ]₀ ®⟨ l ⟩
                       erase str t T.[ σ′ T.⇑ ] T.[ v″ ]₀ ∷
                       B [ σ ⇑ ] [ t′ ]₀                                 →⟨ ®∷-⇐* lam-t[σ]∘t′⇒* lam-⌜t⌝[σ′]∘v′⇒* ⟩

                     (lam p t [ σ ]) ∘⟨ p ⟩ t′ ®⟨ l ⟩
                       (T.lam (erase str t) T.[ σ′ ]) T.∘⟨ str ⟩ v′ ∷
                       B [ σ ⇑ ] [ t′ ]₀                                 ≡⟨ PE.cong₂ (_®⟨_⟩_∷_ _ _)
                                                                              (PE.cong (T._∘⟨ _ ⟩ _) $ PE.cong T._[ _ ] $ PE.sym $
                                                                               lam-≢𝟘 (str T.== T.non-strict) p≢𝟘)
                                                                              PE.refl ⟩→
                     (lam p t [ σ ]) ∘⟨ p ⟩ t′ ®⟨ l ⟩
                       (erase str (lam p t) T.[ σ′ ]) T.∘⟨ str ⟩ v′ ∷
                       B [ σ ⇑ ] [ t′ ]₀                                 □)
            )
      ) }
    where
    open Graded.Erasure.Target.Reasoning

opaque

  -- Validity of _∘⟨_⟩_.

  ∘ʳ :
    Γ ⊢ u ∷ A →
    γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ] Π p , q ▷ A ▹ B →
    δ ▸ Γ ⊩ʳ⟨ l′ ⟩ u ∷[ m ᵐ· p ] A →
    γ +ᶜ p ·ᶜ δ ▸ Γ ⊩ʳ⟨ l ⟩ t ∘⟨ p ⟩ u ∷[ m ] B [ u ]₀
  ∘ʳ {Γ} {u} {A} {γ} {l} {t} {m} {p} {q} {B} {δ} {l′} ⊢u ⊩ʳt ⊩ʳu =
    case I.⊩ᵛΠΣ⇔ .proj₁ $ ▸⊩ʳ∷⇔ .proj₁ ⊩ʳt .proj₁ of λ
      (_ , ⊩A , ⊩B) →
    case fundamental-⊩ᵛ∷ ⊢u of λ
      ⊩u →
    case ⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]₀ ⊩B ⊩u of λ
      ⊩B[u] →
    case PE.singleton m of λ {
      (𝟘ᵐ , PE.refl) → ▸⊩ʳ∷[𝟘ᵐ] ⊩B[u];
      (𝟙ᵐ , PE.refl) →
    ▸⊩ʳ∷⇔ .proj₂
      ( ⊩B[u]
      , λ {σ = σ} {σ′ = σ′} σ®σ′ →
          case escape-®∷[]◂ σ®σ′ of λ
            ⊩σ →

          case
            (t ∘⟨ 𝟘 ⟩ u) [ σ ] ®⟨ l ⟩
              app-𝟘 str (erase str t T.[ σ′ ]) ∷ B [ σ ⇑ ] [ u [ σ ] ]₀  ≡⟨ PE.cong (flip (_®⟨_⟩_∷_ _ _) _) $ PE.sym $
                                                                            app-𝟘-[] (erase str t) ⟩→
            (t ∘⟨ 𝟘 ⟩ u) [ σ ] ®⟨ l ⟩
              app-𝟘 str (erase str t) T.[ σ′ ] ∷ B [ σ ⇑ ] [ u [ σ ] ]₀  ≡⟨ PE.cong (flip (_®⟨_⟩_∷_ _ _) _) $ PE.cong T._[ _ ] $ PE.sym
                                                                            ∘-𝟘 ⟩→
            (t ∘⟨ 𝟘 ⟩ u) [ σ ] ®⟨ l ⟩ erase str (t ∘⟨ 𝟘 ⟩ u) T.[ σ′ ] ∷
              B [ σ ⇑ ] [ u [ σ ] ]₀                                     □
          of λ
            𝟘-lemma →

          case
            (λ (p≢𝟘 : p PE.≢ 𝟘) →

               case PE.sym $ ≢𝟘→⌞⌟≡𝟙ᵐ p≢𝟘 of λ
                 𝟙ᵐ≡⌞p⌟ →

               case                                             $⟨ σ®σ′ ⟩

                 σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ γ +ᶜ p ·ᶜ δ                 →⟨ (subsumption-®∷[]◂ λ x →

                   (γ +ᶜ p ·ᶜ δ) ⟨ x ⟩ PE.≡ 𝟘                         →⟨ proj₂ ∘→ +ᶜ-positive-⟨⟩ γ ⟩
                   (p ·ᶜ δ) ⟨ x ⟩ PE.≡ 𝟘                              →⟨ ·ᶜ-zero-product-⟨⟩ δ ⟩
                   p PE.≡ 𝟘 ⊎ δ ⟨ x ⟩ PE.≡ 𝟘                          →⟨ (λ { (inj₁ p≡𝟘)    → ⊥-elim (p≢𝟘 p≡𝟘)
                                                                            ; (inj₂ δ⟨x⟩≡𝟘) → δ⟨x⟩≡𝟘
                                                                            }) ⟩
                   δ ⟨ x ⟩ PE.≡ 𝟘                                     □) ⟩

                 σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ δ                           ≡⟨ PE.cong₃ (_®_∷[_]_◂_ _ _) 𝟙ᵐ≡⌞p⌟ PE.refl PE.refl ⟩→

                 σ ® σ′ ∷[ ⌞ p ⌟ ] Γ ◂ δ                        →⟨ ▸⊩ʳ∷⇔ .proj₁ ⊩ʳu .proj₂ ⟩

                 u [ σ ] ®⟨ l′ ⟩ erase str u T.[ σ′ ] ∷
                   A [ σ ] ◂ ⌜ ⌞ p ⌟ ⌝                          →⟨ level-®∷ (⊩ᵛ→⊩ˢ∷→⊩[] ⊩A ⊩σ) ∘→
                                                                   ®∷→®∷◂ω (non-trivial ∘→ PE.trans (PE.cong ⌜_⌝ 𝟙ᵐ≡⌞p⌟)) ⟩
                 u [ σ ] ®⟨ l ⟩ erase str u T.[ σ′ ] ∷ A [ σ ]  □
               of λ
                 u[σ]® →

               (u [ σ ] ®⟨ l ⟩ erase str u T.[ σ′ ] ∷ A [ σ ] →
                (t ∘⟨ p ⟩ u) [ σ ] ®⟨ l ⟩
                  (erase str t T.∘⟨ str ⟩ erase str u) T.[ σ′ ] ∷
                  B [ σ ⇑ ] [ u [ σ ] ]₀)                          →⟨ _$ u[σ]® ⟩

               (t ∘⟨ p ⟩ u) [ σ ] ®⟨ l ⟩
                 (erase str t T.∘⟨ str ⟩ erase str u) T.[ σ′ ] ∷
                 B [ σ ⇑ ] [ u [ σ ] ]₀                            ≡⟨ PE.cong (flip (_®⟨_⟩_∷_ _ _) _) $ PE.cong T._[ _ ] $ PE.sym $
                                                                      ∘-≢𝟘 p≢𝟘 ⟩→
               (t ∘⟨ p ⟩ u) [ σ ] ®⟨ l ⟩
                 erase str (t ∘⟨ p ⟩ u) T.[ σ′ ] ∷
                 B [ σ ⇑ ] [ u [ σ ] ]₀                            □)
          of λ
            ≢𝟘-lemma →                                                   $⟨ σ®σ′ ⟩

          σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ γ +ᶜ p ·ᶜ δ                                 →⟨ subsumption-®∷[]◂ (λ _ → proj₁ ∘→ +ᶜ-positive-⟨⟩ γ) ⟩

          σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ γ                                           →⟨ ®∷→®∷◂ω non-trivial ∘→
                                                                            ▸⊩ʳ∷⇔ .proj₁ ⊩ʳt .proj₂ ⟩
          (t [ σ ] ®⟨ l ⟩ erase str t T.[ σ′ ] ∷
             (Π p , q ▷ A ▹ B) [ σ ])                                    →⟨ (λ hyp → hyp _ $ escape-⊩∷ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩u ⊩σ) ∘→
                                                                            proj₂ ∘→ proj₂ ∘→ ®∷Π⇔ .proj₁ ⟩
          (p PE.≡ 𝟘 →
           (t ∘⟨ 𝟘 ⟩ u) [ σ ] ®⟨ l ⟩ app-𝟘 str (erase str t T.[ σ′ ]) ∷
              B [ σ ⇑ ] [ u [ σ ] ]₀) ×
          (p PE.≢ 𝟘 →
           ∀ v′ → u [ σ ] ®⟨ l ⟩ v′ ∷ A [ σ ] →
           (t ∘⟨ p ⟩ u) [ σ ] ®⟨ l ⟩
             (erase str t T.[ σ′ ]) T.∘⟨ str ⟩ v′ ∷
             B [ σ ⇑ ] [ u [ σ ] ]₀)                                     →⟨ (λ (≡𝟘→ , ≢𝟘→) →
                                                                               case is-𝟘? p of λ where
                                                                                 (yes PE.refl) → 𝟘-lemma (≡𝟘→ PE.refl)
                                                                                 (no p≢𝟘)      → ≢𝟘-lemma p≢𝟘 (≢𝟘→ p≢𝟘 _)) ⟩
          ((t ∘⟨ p ⟩ u) [ σ ] ®⟨ l ⟩ erase str (t ∘⟨ p ⟩ u) T.[ σ′ ] ∷
             B [ σ ⇑ ] [ u [ σ ] ]₀)                                     ≡⟨ PE.cong (_®⟨_⟩_∷_ _ _ _) $ PE.sym $
                                                                            singleSubstLift B _ ⟩→
          ((t ∘⟨ p ⟩ u) [ σ ] ®⟨ l ⟩
             erase str (t ∘⟨ p ⟩ u) T.[ σ′ ] ∷ B [ u ]₀ [ σ ])           →⟨ ®∷→®∷◂ ⟩

          (t ∘⟨ p ⟩ u) [ σ ] ®⟨ l ⟩
            erase str (t ∘⟨ p ⟩ u) T.[ σ′ ] ∷ B [ u ]₀ [ σ ] ◂ 𝟙         □
      ) }

------------------------------------------------------------------------
-- Lemmas related to Σ

opaque

  -- Validity of prod.

  prodʳ :
    (_⊕ᶜ_ : Conₘ n → Conₘ n → Conₘ n) →
    (∀ {x γ δ} →
     (γ ⊕ᶜ δ) ⟨ x ⟩ PE.≡ 𝟘 → γ ⟨ x ⟩ PE.≡ 𝟘 × δ ⟨ x ⟩ PE.≡ 𝟘) →
    Σ-allowed s p q →
    Γ ∙ A ⊩ᵛ⟨ l ⟩ B →
    Γ ⊩ᵛ⟨ l ⟩ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    γ ▸ Γ ⊩ʳ⟨ l′ ⟩ t ∷[ m ᵐ· p ] A →
    δ ▸ Γ ⊩ʳ⟨ l″ ⟩ u ∷[ m ] B [ t ]₀ →
    ((p ·ᶜ γ) ⊕ᶜ δ) ▸ Γ ⊩ʳ⟨ l ⟩ prod s p t u ∷[ m ] Σ⟨ s ⟩ p , q ▷ A ▹ B
  prodʳ
    {s} {p} {Γ} {A} {l} {B} {t} {u} {γ} {m} {δ}
    _⊕ᶜ_ ⊕ᶜ-positive-⟨⟩ ok ⊩B ⊩t ⊢u ⊩ʳt ⊩ʳu =
    case wf-⊩ᵛ∷ ⊩t of λ
      ⊩A →
    case I.ΠΣᵛ ok ⊩A ⊩B of λ
      ⊩ΣAB →
    case PE.singleton m of λ {
      (𝟘ᵐ , PE.refl) → ▸⊩ʳ∷[𝟘ᵐ] ⊩ΣAB;
      (𝟙ᵐ , PE.refl) →
    ▸⊩ʳ∷⇔ .proj₂
      ( ⊩ΣAB
      , λ {σ = σ} {σ′ = σ′} σ®σ′ →
          case escape-®∷[]◂ σ®σ′ of λ
            ⊩σ →

          case                                                            $⟨ σ®σ′ ⟩
            σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ ((p ·ᶜ γ) ⊕ᶜ δ)                            →⟨ subsumption-®∷[]◂ (λ _ → proj₂ ∘→ ⊕ᶜ-positive-⟨⟩) ⟩
            σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ δ                                          →⟨ level-®∷ (⊩ᵛ→⊩ˢ∷→⊩[] (⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]₀ ⊩B ⊩t) ⊩σ) ∘→
                                                                             ®∷→®∷◂ω non-trivial ∘→
                                                                             ▸⊩ʳ∷⇔ .proj₁ ⊩ʳu .proj₂ ⟩
            u [ σ ] ®⟨ l ⟩ erase str u T.[ σ′ ] ∷ B [ t ]₀ [ σ ]          ≡⟨ PE.cong (_®⟨_⟩_∷_ _ _ _) (singleSubstLift B _) ⟩→
            u [ σ ] ®⟨ l ⟩ erase str u T.[ σ′ ] ∷ B [ σ ⇑ ] [ t [ σ ] ]₀  □
          of λ
            u[σ]® →

          case
            (λ p≢𝟘 →
               case PE.sym $ ≢𝟘→⌞⌟≡𝟙ᵐ p≢𝟘 of λ
                 𝟙ᵐ≡⌞p⌟ →                                     $⟨ σ®σ′ ⟩

               σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ ((p ·ᶜ γ) ⊕ᶜ δ)             →⟨ (subsumption-®∷[]◂ λ x →
                 ((p ·ᶜ γ) ⊕ᶜ δ) ⟨ x ⟩ PE.≡ 𝟘                       →⟨ proj₁ ∘→ ⊕ᶜ-positive-⟨⟩ ⟩
                 (p ·ᶜ γ) ⟨ x ⟩ PE.≡ 𝟘                              →⟨ ·ᶜ-zero-product-⟨⟩ γ ⟩
                 p PE.≡ 𝟘 ⊎ γ ⟨ x ⟩ PE.≡ 𝟘                          →⟨ (λ { (inj₁ p≡𝟘)    → ⊥-elim (p≢𝟘 p≡𝟘)
                                                                          ; (inj₂ γ⟨x⟩≡𝟘) → γ⟨x⟩≡𝟘
                                                                          }) ⟩
                 γ ⟨ x ⟩ PE.≡ 𝟘                                     □) ⟩

               σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ γ                           ≡⟨ PE.cong₃ (_®_∷[_]_◂_ _ _) 𝟙ᵐ≡⌞p⌟ PE.refl PE.refl ⟩→

               σ ® σ′ ∷[ 𝟙ᵐ ᵐ· p ] Γ ◂ γ                      →⟨ level-®∷ (⊩ᵛ→⊩ˢ∷→⊩[] ⊩A ⊩σ) ∘→
                                                                 ®∷→®∷◂ω (non-trivial ∘→ PE.trans (PE.cong ⌜_⌝ 𝟙ᵐ≡⌞p⌟)) ∘→
                                                                 ▸⊩ʳ∷⇔ .proj₁ ⊩ʳt .proj₂ ⟩
               t [ σ ] ®⟨ l ⟩ erase str t T.[ σ′ ] ∷ A [ σ ]  □)
          of λ
            t[σ]® →

          case
            (∃ λ v₂ → erase str u T.[ σ′ ] T.⇒* v₂ ×
             (p PE.≢ 𝟘 →
              ∃ λ v₁ → erase str t T.[ σ′ ] T.⇒* v₁ ×
              T.prod⟨ str ⟩ (erase str t T.[ σ′ ])
                (erase str u T.[ σ′ ]) T.⇒*
                T.prod v₁ v₂))
          ∋ (case PE.singleton str of λ where
               (T.non-strict , PE.refl) →
                 _ , T.refl , λ _ → _ , T.refl , T.refl
               (T.strict     , PE.refl) →
                 case reduces-to-value PE.refl u[σ]® of λ
                   (v₂ , v₂-val , u[σ′]⇒*v₂) →
                   v₂ , u[σ′]⇒*v₂
                 , λ p≢𝟘 →
                     case reduces-to-value PE.refl (t[σ]® p≢𝟘) of λ
                       (v₁ , v₁-val , t[σ′]⇒*v₁) →
                       v₁ , t[σ′]⇒*v₁
                     , (T.lam (T.lam (T.prod (T.var x1) (T.var x0)))
                          T.∘⟨ T.strict ⟩ (erase T.strict t T.[ σ′ ])
                          T.∘⟨ T.strict ⟩ (erase T.strict u T.[ σ′ ])  ⇒*⟨ TP.app-subst* $ TP.app-subst*-arg T.lam t[σ′]⇒*v₁ ⟩

                        T.lam (T.lam (T.prod (T.var x1) (T.var x0)))
                          T.∘⟨ T.strict ⟩ v₁
                          T.∘⟨ T.strict ⟩ (erase T.strict u T.[ σ′ ])  ⇒⟨ T.app-subst $ T.β-red v₁-val ⟩

                        T.lam (T.prod (T.wk1 v₁) (T.var x0))
                          T.∘⟨ T.strict ⟩ (erase T.strict u T.[ σ′ ])  ⇒*⟨ TP.app-subst*-arg T.lam u[σ′]⇒*v₂ ⟩

                        T.lam (T.prod (T.wk1 v₁) (T.var x0))
                          T.∘⟨ T.strict ⟩ v₂                           ⇒⟨ T.β-red v₂-val ⟩

                        T.prod (T.wk1 v₁ T.[ v₂ ]₀) v₂                 ≡⟨ PE.cong (flip T.prod v₂) $ TP.wk1-sgSubst _ _ ⟩⇒

                        T.prod v₁ v₂                                   ∎⇒))
          of λ
            (v₂ , u[σ′]⇒*v₂ , rest) →

          ®∷→®∷◂ $
          ®∷Σ⇔ .proj₂
            ( ⊩ᵛ→⊩ˢ∷→⊩[] ⊩ΣAB ⊩σ
            , t [ σ ] , u [ σ ] , v₂
            , (_⊢_⇒*_∷_.id $
               ⊢prod (escape $ ⊩ᵛ→⊩ˢ∷→⊩[⇑] ⊩B ⊩σ)
                 (escape-⊩∷ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩t ⊩σ)
                 (PE.subst (_⊢_∷_ _ _) (singleSubstLift B _) $
                  substitutionTerm ⊢u (escape-⊩ˢ∷ ⊩σ .proj₂) ⊢Δ)
                 ok)
            , ®∷-⇒* u[σ′]⇒*v₂ u[σ]®
            , (λ p≡𝟘 →
                 erase str (prod s p t u) T.[ σ′ ]  ≡⟨ PE.cong T._[ _ ] $ prod-𝟘 s p≡𝟘 ⟩⇒
                 erase str u T.[ σ′ ]               ⇒*⟨ u[σ′]⇒*v₂ ⟩
                 v₂                                 ∎⇒)
            , (λ p≢𝟘 →
                 case rest p≢𝟘 of λ
                   (v₁ , t[σ′]⇒*v₁ , t,u[σ′]⇒*v₁,v₂) →
                   v₁
                 , (erase str (prod s p t u) T.[ σ′ ]                   ≡⟨ PE.cong T._[ _ ] $ prod-ω s p≢𝟘 ⟩⇒

                    T.prod⟨ str ⟩ (erase str t) (erase str u) T.[ σ′ ]  ≡⟨ TP.prod⟨⟩-[] ⟩⇒

                    T.prod⟨ str ⟩ (erase str t T.[ σ′ ])
                      (erase str u T.[ σ′ ])                            ⇒*⟨ t,u[σ′]⇒*v₁,v₂ ⟩

                    T.prod v₁ v₂                                        ∎⇒)
                 , ®∷-⇒* t[σ′]⇒*v₁ (t[σ]® p≢𝟘))
            )
      ) }
    where
    open Graded.Erasure.Target.Reasoning

opaque

  -- Validity of prodˢ.

  prodˢʳ :
    Σˢ-allowed p q →
    Γ ∙ A ⊩ᵛ⟨ l ⟩ B →
    Γ ⊩ᵛ⟨ l ⟩ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    γ ▸ Γ ⊩ʳ⟨ l′ ⟩ t ∷[ m ᵐ· p ] A →
    δ ▸ Γ ⊩ʳ⟨ l″ ⟩ u ∷[ m ] B [ t ]₀ →
    p ·ᶜ γ ∧ᶜ δ ▸ Γ ⊩ʳ⟨ l ⟩ prodˢ p t u ∷[ m ] Σˢ p , q ▷ A ▹ B
  prodˢʳ = prodʳ _∧ᶜ_ (λ {_} {γ = γ} → ∧ᶜ-positive-⟨⟩ γ)

opaque

  -- Validity of prodʷ.

  prodʷʳ :
    Σʷ-allowed p q →
    Γ ∙ A ⊩ᵛ⟨ l ⟩ B →
    Γ ⊩ᵛ⟨ l ⟩ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    γ ▸ Γ ⊩ʳ⟨ l′ ⟩ t ∷[ m ᵐ· p ] A →
    δ ▸ Γ ⊩ʳ⟨ l″ ⟩ u ∷[ m ] B [ t ]₀ →
    p ·ᶜ γ +ᶜ δ ▸ Γ ⊩ʳ⟨ l ⟩ prodʷ p t u ∷[ m ] Σʷ p , q ▷ A ▹ B
  prodʷʳ = prodʳ _+ᶜ_ (λ {_} {γ = γ} → +ᶜ-positive-⟨⟩ γ)

opaque

  -- Validity of fst.

  fstʳ :
    γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ] Σˢ p , q ▷ A ▹ B →
    γ ▸[ m ] fst p t →
    γ ▸ Γ ⊩ʳ⟨ l ⟩ fst p t ∷[ m ] A
  fstʳ {γ} {Γ} {l} {t} {m} {p} {q} {A} {B} ⊩ʳt ▸fst-t =
    case ▸⊩ʳ∷⇔ .proj₁ ⊩ʳt .proj₁ of λ
      ⊩ΣAB →
    case I.⊩ᵛΠΣ⇔ .proj₁ ⊩ΣAB of λ
      (ok , ⊩A , ⊩B) →
    case PE.singleton m of λ {
      (𝟘ᵐ , PE.refl) → ▸⊩ʳ∷[𝟘ᵐ] ⊩A;
      (𝟙ᵐ , PE.refl) →
    case
      (λ p≡𝟘 →
         let open Tools.Reasoning.PartialOrder ≤-poset in
         𝟘≰𝟙 $ begin
           𝟘  ≡˘⟨ p≡𝟘 ⟩
           p  ≤⟨ InvUsageFst.mp-condition (inv-usage-fst ▸fst-t) PE.refl ⟩
           𝟙  ∎)
    of λ
      p≢𝟘 →
    ▸⊩ʳ∷⇔ .proj₂
      ( ⊩A
      , λ {σ = σ} {σ′ = σ′} σ®σ′ →
          case escape-®∷[]◂ σ®σ′ of λ
            ⊩σ →                                                         $⟨ σ®σ′ ⟩

          σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ γ                                           →⟨ level-®∷ (⊩ᵛ→⊩ˢ∷→⊩[] ⊩ΣAB ⊩σ) ∘→
                                                                            ®∷→®∷◂ω non-trivial ∘→
                                                                            ▸⊩ʳ∷⇔ .proj₁ ⊩ʳt .proj₂ ⟩
          (t [ σ ] ®⟨ l ⟩ erase str t T.[ σ′ ] ∷
             (Σˢ p , q ▷ A ▹ B) [ σ ])                                   →⟨ proj₂ ∘→ ®∷Σω⇔ p≢𝟘 .proj₁ ⟩

          (∃₄ λ t₁ t₂ v₁ v₂ →
           Δ ⊢ t [ σ ] ⇒* prodˢ p t₁ t₂ ∷ (Σˢ p , q ▷ A ▹ B) [ σ ] ×
           erase str t T.[ σ′ ] T.⇒* T.prod v₁ v₂ ×
           t₁ ®⟨ l ⟩ v₁ ∷ A [ σ ] ×
           t₂ ®⟨ l ⟩ v₂ ∷ B [ σ ⇑ ] [ t₁ ]₀)                             →⟨ (λ (t₁ , t₂ , v₁ , v₂ ,
                                                                                t[σ]⇒*t₁,t₂ , t[σ′]⇒*v₂,v₂ , t₁®v₁ , _) →
                                                                               case inversion-prod-Σ $
                                                                                    syntacticRedTerm t[σ]⇒*t₁,t₂ .proj₂ .proj₂ of λ
                                                                                 (⊢t₁ , ⊢t₂ , _) →
                                                                               ®∷-⇐*
                                                                                 (let open RR in
             fst p (t [ σ ])                                                        ⇒*⟨ fst-subst*′ t[σ]⇒*t₁,t₂ ⟩
             fst p (prodˢ p t₁ t₂)                                                  ⇒⟨ Σ-β₁-⇒ (escape $ ⊩ᵛ→⊩ˢ∷→⊩[⇑] ⊩B ⊩σ) ⊢t₁ ⊢t₂ ok ⟩∎
             t₁                                                                     ∎)
                                                                                 (let open Graded.Erasure.Target.Reasoning in
             T.fst (erase str t T.[ σ′ ])                                           ⇒*⟨ TP.fst-subst* t[σ′]⇒*v₂,v₂ ⟩
             T.fst (T.prod v₁ v₂)                                                   ⇒⟨ T.Σ-β₁ ⟩
             v₁                                                                     ∎⇒)
                                                                                 t₁®v₁) ⟩

          (fst p t [ σ ] ®⟨ l ⟩ T.fst (erase str t) T.[ σ′ ] ∷ A [ σ ])  ≡⟨ PE.cong₂ (_®⟨_⟩_∷_ _ _)
                                                                              (PE.cong T._[ _ ] $ PE.sym $ fst-≢𝟘 p≢𝟘) PE.refl ⟩→

          (fst p t [ σ ] ®⟨ l ⟩ erase str (fst p t) T.[ σ′ ] ∷ A [ σ ])  →⟨ ®∷→®∷◂ ⟩

          fst p t [ σ ] ®⟨ l ⟩ erase str (fst p t) T.[ σ′ ] ∷ A [ σ ] ◂
            𝟙                                                            □
      ) }

opaque

  -- Validity of snd.

  sndʳ :
    Γ ⊢ t ∷ Σˢ p , q ▷ A ▹ B →
    γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ] Σˢ p , q ▷ A ▹ B →
    γ ▸ Γ ⊩ʳ⟨ l ⟩ snd p t ∷[ m ] B [ fst p t ]₀
  sndʳ {Γ} {t} {p} {q} {A} {B} {γ} {l} {m} ⊢t ⊩ʳt =
    case ▸⊩ʳ∷⇔ .proj₁ ⊩ʳt .proj₁ of λ
      ⊩ΣAB →
    case I.⊩ᵛΠΣ⇔ .proj₁ ⊩ΣAB of λ
      (ok , _ , ⊩B) →
    case ⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]₀ ⊩B (fundamental-⊩ᵛ∷ (fstⱼ′ ⊢t)) of λ
      ⊩B[fst-t] →
    case PE.singleton m of λ {
      (𝟘ᵐ , PE.refl) → ▸⊩ʳ∷[𝟘ᵐ] ⊩B[fst-t];
      (𝟙ᵐ , PE.refl) →
    ▸⊩ʳ∷⇔ .proj₂
      ( ⊩B[fst-t]
      , λ {σ = σ} {σ′ = σ′} σ®σ′ →
          case escape-®∷[]◂ σ®σ′ of λ
            ⊩σ →
          case escape $ ⊩ᵛ→⊩ˢ∷→⊩[⇑] ⊩B ⊩σ of λ
            ⊢B[σ⇑] →                                                      $⟨ σ®σ′ ⟩

          σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ γ                                            →⟨ level-®∷ (⊩ᵛ→⊩ˢ∷→⊩[] ⊩ΣAB ⊩σ) ∘→
                                                                             ®∷→®∷◂ω non-trivial ∘→
                                                                             ▸⊩ʳ∷⇔ .proj₁ ⊩ʳt .proj₂ ⟩
          (t [ σ ] ®⟨ l ⟩ erase str t T.[ σ′ ] ∷
             (Σˢ p , q ▷ A ▹ B) [ σ ])                                    →⟨ proj₂ ∘→ ®∷Σ⇔ .proj₁ ⟩

          (∃₃ λ t₁ t₂ v₂ →
           Δ ⊢ t [ σ ] ⇒* prodˢ p t₁ t₂ ∷ (Σˢ p , q ▷ A ▹ B) [ σ ] ×
           t₂ ®⟨ l ⟩ v₂ ∷ B [ σ ⇑ ] [ t₁ ]₀ ×
           (p PE.≡ 𝟘 → erase str t T.[ σ′ ] T.⇒* v₂) ×
           (p PE.≢ 𝟘 →
            ∃ λ v₁ → erase str t T.[ σ′ ] T.⇒* T.prod v₁ v₂ ×
            t₁ ®⟨ l ⟩ v₁ ∷ A [ σ ]))                                      →⟨ (λ (t₁ , t₂ , v₂ , t[σ]⇒*t₁,t₂ , t₂®v₂ , 𝟘-hyp , ≢𝟘-hyp) →
                                                                                case inversion-prod-Σ $
                                                                                     syntacticRedTerm t[σ]⇒*t₁,t₂ .proj₂ .proj₂ of λ
                                                                                  (⊢t₁ , ⊢t₂ , _) →
                                                                                ®∷-⇐*
                                                                                  (let open RR in
            snd p (t [ σ ])       ∷ B [ σ ⇑ ] [ fst p (t [ σ ]) ]₀                   ⇒*⟨ snd-subst* t[σ]⇒*t₁,t₂ ⟩∷
                                                                                       ⟨ ≅-eq $ escape-⊩≡ $
                                                                                         ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ (refl-⊩ᵛ≡ ⊩B) (refl-⊩ˢ≡∷ ⊩σ) $
                                                                                         reducible-⊩≡∷ $ subset*Term $ fst-subst*′ t[σ]⇒*t₁,t₂ ⟩⇒
            snd p (prodˢ p t₁ t₂) ∷ B [ σ ⇑ ] [ fst p (prodˢ p t₁ t₂) ]₀             ⇒⟨ Σ-β₂-⇒ ⊢B[σ⇑] ⊢t₁ ⊢t₂ ok ⟩∎∷
            t₂                                                                       ∎)
                                                                                  (let open Graded.Erasure.Target.Reasoning in
                                                                                   case is-𝟘? p of λ {
                                                                                     (no p≢𝟘) →
                                                                                       case ≢𝟘-hyp p≢𝟘 of λ
                                                                                         (v₁ , t[σ′]⇒*v₁,v₂ , _) →
            erase str (snd p t) T.[ σ′ ]                                               ≡⟨ PE.cong T._[ _ ] $ snd-ω p≢𝟘 ⟩⇒
            T.snd (erase str t T.[ σ′ ])                                               ⇒*⟨ TP.snd-subst* t[σ′]⇒*v₁,v₂ ⟩
            T.snd (T.prod v₁ v₂)                                                       ⇒⟨ T.Σ-β₂ ⟩
            v₂                                                                         ∎⇒;

                                                                                     (yes PE.refl) →
            erase str (snd 𝟘 t) T.[ σ′ ]                                               ≡⟨ PE.cong T._[ _ ] $ snd-𝟘 PE.refl ⟩⇒
            erase str t T.[ σ′ ]                                                       ⇒*⟨ 𝟘-hyp PE.refl ⟩
            v₂                                                                         ∎⇒ }) $
                                                                                conv-®∷
                                                                                  (let open RR in
                                                                                   ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ (refl-⊩ᵛ≡ ⊩B) (refl-⊩ˢ≡∷ ⊩σ) $
                                                                                   sym-⊩≡∷ $ reducible-⊩≡∷ $ subset*Term (
            fst p (t [ σ ])                                                          ⇒*⟨ fst-subst*′ t[σ]⇒*t₁,t₂ ⟩
            fst p (prodˢ p t₁ t₂)                                                    ⇒⟨ Σ-β₁-⇒ ⊢B[σ⇑] ⊢t₁ ⊢t₂ ok ⟩∎
            t₁                                                                       ∎))
                                                                                  t₂®v₂) ⟩
          (snd p t [ σ ] ®⟨ l ⟩ erase str (snd p t) T.[ σ′ ] ∷
             B [ σ ⇑ ] [ fst p t [ σ ] ]₀)                                ≡⟨ PE.cong (_®⟨_⟩_∷_ _ _ _) $ PE.sym $
                                                                             singleSubstLift B _ ⟩→
          (snd p t [ σ ] ®⟨ l ⟩ erase str (snd p t) T.[ σ′ ] ∷
             B [ fst p t ]₀ [ σ ])                                        →⟨ ®∷→®∷◂ ⟩

          snd p t [ σ ] ®⟨ l ⟩ erase str (snd p t) T.[ σ′ ] ∷
            B [ fst p t ]₀ [ σ ] ◂ 𝟙                                      □
      ) }

opaque

  -- Validity of prodrec.

  prodrecʳ :
    {Γ : Con Term n} →
    Γ ∙ Σʷ p , q ▷ A ▹ B ⊩ᵛ⟨ l ⟩ C →
    Γ ⊢ t ∷ Σʷ p , q ▷ A ▹ B →
    Γ ∙ A ∙ B ⊢ u ∷ C [ prodʷ p (var x1) (var x0) ]↑² →
    γ ▸ Γ ⊩ʳ⟨ l′ ⟩ t ∷[ m ᵐ· r ] Σʷ p , q ▷ A ▹ B →
    δ ∙ ⌜ m ⌝ · r · p ∙ ⌜ m ⌝ · r ▸ Γ ∙ A ∙ B ⊩ʳ⟨ l″ ⟩ u ∷[ m ]
      C [ prodʷ p (var x1) (var x0) ]↑² →
    (r PE.≡ 𝟘 → k PE.≡ 0) →
    r ·ᶜ γ +ᶜ δ ▸ Γ ⊩ʳ⟨ l ⟩ prodrec r p q′ C t u ∷[ m ] C [ t ]₀
  prodrecʳ
    {n} {p} {q} {A} {B} {l} {C} {t} {u} {γ} {l′} {m} {r} {δ} {l″} {q′}
    {Γ} ⊩C ⊢t ⊢u ⊩ʳt ⊩ʳu r≡𝟘→k≡0 =
    case PE.singleton m of λ {
      (𝟘ᵐ , PE.refl) → ▸⊩ʳ∷[𝟘ᵐ] ⊩C[t];
      (𝟙ᵐ , PE.refl) →
    ▸⊩ʳ∷⇔ .proj₂
      ( ⊩C[t]
      , λ {σ = σ} {σ′ = σ′} σ®σ′ →
          let open Lemmas PE.refl σ®σ′ in                  $⟨ σ®σ′ ⟩

          σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ r ·ᶜ γ +ᶜ δ                   →⟨ subsumption-®∷[]◂ (λ _ → proj₂ ∘→ +ᶜ-positive-⟨⟩ (_ ·ᶜ γ)) ⟩

          σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ δ                             →⟨ (λ σ®σ′ →
                                                                 ®∷[]∙◂∙⇔′ .proj₂
                                                                   ( ⊩B
                                                                   , ( _
                                                                     , (reducible-⊩∷ $
                                                                        PE.subst (_⊢_∷_ _ _) (singleSubstComp _ _ B)
                                                                          ⊢t₂)
                                                                     )
                                                                   , (_ , t₂®v₂′)
                                                                   , ®∷[]∙◂∙⇔′ .proj₂
                                                                       (⊩A , (_ , reducible-⊩∷ ⊢t₁) , (_ , t₁®v₁′) , σ®σ′)
                                                                   )) ⟩
          consSubst (consSubst σ t₁) t₂ ®
            T.consSubst (T.consSubst σ′ v₁) v₂ ∷[ 𝟙ᵐ ]
            Γ ∙ A ∙ B ◂ δ ∙ 𝟙 · r · p ∙ 𝟙 · r              →⟨ ®∷→®∷◂ω non-trivial ∘→
                                                              ▸⊩ʳ∷⇔ .proj₁ ⊩ʳu .proj₂ ⟩
          (u [ consSubst (consSubst σ t₁) t₂ ] ®⟨ l″ ⟩
             erase str u
               T.[ T.consSubst (T.consSubst σ′ v₁) v₂ ] ∷
             C [ prodʷ p (var x1) (var x0) ]↑²
               [ consSubst (consSubst σ t₁) t₂ ])          →⟨ conv-®∷ C[1,0]↑²[σ,t₁,t₂]≡C[σ⇑][t[σ]] ⟩

          (u [ consSubst (consSubst σ t₁) t₂ ] ®⟨ l ⟩
             erase str u
               T.[ T.consSubst (T.consSubst σ′ v₁) v₂ ] ∷
             C [ σ ⇑ ] [ t [ σ ] ]₀)                       →⟨ ®∷-⇐* ⇒*u[σ,t₁,t₂] ⇒*u[σ′,v₁,v₂] ⟩

          (prodrec r p q′ C t u [ σ ] ®⟨ l ⟩
             erase str (prodrec r p q′ C t u) T.[ σ′ ] ∷
             C [ σ ⇑ ] [ t [ σ ] ]₀)                       →⟨ ®∷→®∷◂ ∘→
                                                              PE.subst (_®⟨_⟩_∷_ _ _ _) (PE.sym $ singleSubstLift C _) ⟩
          prodrec r p q′ C t u [ σ ] ®⟨ l ⟩
            erase str (prodrec r p q′ C t u) T.[ σ′ ] ∷
            C [ t ]₀ [ σ ] ◂ 𝟙                             □
      ) }
    where
    open Tools.Reasoning.PropositionalEquality

    opaque

      ⊩t : ∃ λ l → Γ ⊩ᵛ⟨ l ⟩ t ∷ Σʷ p , q ▷ A ▹ B
      ⊩t = _ , fundamental-⊩ᵛ∷ ⊢t

    opaque

      ⊩C[t] : Γ ⊩ᵛ⟨ l ⟩ C [ t ]₀
      ⊩C[t] = ⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]₀ ⊩C (⊩t .proj₂)

    opaque

      ⊢A,⊢B,ok : Γ ⊢ A × Γ ∙ A ⊢ B × Σʷ-allowed p q
      ⊢A,⊢B,ok =
        inversion-ΠΣ $ syntacticTerm $ escape-⊩ᵛ∷ $ ⊩t .proj₂

    opaque

      ⊩A : ∃ λ l → Γ ⊩ᵛ⟨ l ⟩ A
      ⊩A = _ , fundamental-⊩ᵛ (⊢A,⊢B,ok .proj₁)

    opaque

      ⊩B : ∃ λ l → Γ ∙ A ⊩ᵛ⟨ l ⟩ B
      ⊩B = _ , fundamental-⊩ᵛ (⊢A,⊢B,ok .proj₂ .proj₁)

    -- Some assumptions that are used in the proof.

    record Prodrec-assumptions
             (σ : Subst k n) (σ′ : T.Subst k n) : Set a where
      no-eta-equality
      field
        {l₁ l₂}       : TypeLevel
        t₁ t₂         : Term k
        v₁ v₂         : T.Term k
        t₁®v₁         : t₁ ®⟨ l₁ ⟩ v₁ ∷ A [ σ ] ◂ r · p
        t₂®v₂         : t₂ ®⟨ l₂ ⟩ v₂ ∷ B [ σ ⇑ ] [ t₁ ]₀ ◂ r
        t[σ]⇒*t₁,t₂   : Δ ⊢ t [ σ ] ⇒* prodʷ p t₁ t₂ ∷
                          (Σʷ p , q ▷ A ▹ B) [ σ ]
        ⇒*u[σ′,v₁,v₂] : erase str (prodrec r p q′ C t u) T.[ σ′ ] T.⇒*
                          erase str u
                            T.[ T.consSubst (T.consSubst σ′ v₁) v₂ ]

      private opaque

        ⊢t₁,⊢t₂ : Δ ⊢ t₁ ∷ A [ σ ] × Δ ⊢ t₂ ∷ B [ σ ⇑ ] [ t₁ ]₀
        ⊢t₁,⊢t₂ =
          Σ.map idᶠ proj₁ $
          inversion-prod-Σ $
          syntacticEqTerm (subset*Term t[σ]⇒*t₁,t₂) .proj₂ .proj₂

      opaque

        ⊢t₁ : Δ ⊢ t₁ ∷ A [ σ ]
        ⊢t₁ = ⊢t₁,⊢t₂ .proj₁

      opaque

        ⊢t₂ : Δ ⊢ t₂ ∷ B [ σ ⇑ ] [ t₁ ]₀
        ⊢t₂ = ⊢t₁,⊢t₂ .proj₂

      opaque

        t₁®v₁′ : t₁ ®⟨ l₁ ⟩ v₁ ∷ A [ σ ] ◂ 𝟙 · 𝟙 · r · p
        t₁®v₁′ =
          PE.subst (_®⟨_⟩_∷_◂_ _ _ _ _)
            (r · p          ≡˘⟨ ·-identityˡ _ ⟩
             𝟙 · r · p      ≡˘⟨ ·-identityˡ _ ⟩
             𝟙 · 𝟙 · r · p  ∎)
            t₁®v₁

      opaque

        t₂®v₂′ : t₂ ®⟨ l₂ ⟩ v₂ ∷ B [ consSubst σ t₁ ] ◂ 𝟙 · 𝟙 · r
        t₂®v₂′ =
          PE.subst₂ (_®⟨_⟩_∷_◂_ _ _ _) (singleSubstComp _ _ B)
            (r          ≡˘⟨ ·-identityˡ _ ⟩
             𝟙 · r      ≡˘⟨ ·-identityˡ _ ⟩
             𝟙 · 𝟙 · r  ∎)
            t₂®v₂

    module Lemmas
      (m≡𝟙ᵐ : m PE.≡ 𝟙ᵐ)
      (σ®σ′ : σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ r ·ᶜ γ +ᶜ δ)
      where

      open Graded.Erasure.Target.Reasoning

      private opaque

        ⊩σ : Δ ⊩ˢ σ ∷ Γ
        ⊩σ = escape-®∷[]◂ σ®σ′

      private opaque

        ⊩A[σ] : ∃ λ l → Δ ⊩⟨ l ⟩ A [ σ ]
        ⊩A[σ] = Σ.map idᶠ (flip ⊩ᵛ→⊩ˢ∷→⊩[] ⊩σ) ⊩A

      private opaque

        -- The Prodrec-assumptions hold for σ and σ′ when r is 𝟘:
        --
        -- * In this case the context is empty, so t [ σ ] must reduce
        --   to a pair.
        -- * Furthermore, because r is 𝟘, the components of the pair
        --   are related to anything.

        r≡𝟘-lemma : r PE.≡ 𝟘 → Prodrec-assumptions σ σ′
        r≡𝟘-lemma PE.refl =
          case r≡𝟘→k≡0 PE.refl of λ {
            PE.refl →
          case red-Σ $
               substitutionTerm ⊢t (escape-⊩ˢ∷ ⊩σ .proj₂) ⊢Δ of λ {
            (_ , ne n , _) →
              ⊥-elim (noClosedNe n);
            (_ , prodₙ {t = t₁} {u = t₂} , t[σ]⇒*t₁,t₂) →
          case inversion-prod-Σ $ ⊢u-redₜ t[σ]⇒*t₁,t₂ of λ {
            (⊢t₁ , _ , PE.refl , PE.refl , _) →
          record
            { t₁            = t₁
            ; t₂            = t₂
            ; v₁            = loop str
            ; v₂            = loop str
            ; t₁®v₁         = ®∷◂𝟘 (·-zeroˡ _) (⊩A[σ] .proj₂)
            ; t₂®v₂         = ®∷◂𝟘 PE.refl $
                              ⊩ᵛ→⊩ˢ∷→⊩∷→⊩[⇑][]₀ (⊩B .proj₂) ⊩σ
                                (reducible-⊩∷ ⊢t₁)
            ; t[σ]⇒*t₁,t₂   = redₜ t[σ]⇒*t₁,t₂
            ; ⇒*u[σ′,v₁,v₂] =
                erase str (prodrec 𝟘 p q′ C t u) T.[ σ′ ]               ≡⟨ PE.cong T._[ _ ] $ prodrec-𝟘 q′ C ⟩⇒

                erase str u T.[ loop str , loop str ]₁₀ T.[ σ′ ]        ≡⟨ TP.doubleSubstComp′ (erase _ u) ⟩⇒

                erase str u
                  T.[ T.consSubst (T.consSubst σ′ (loop str T.[ σ′ ]))
                        (loop str T.[ σ′ ]) ]                           ≡⟨ PE.cong (λ t → erase _ u T.[ T.consSubst (T.consSubst _ t) t ])
                                                                           loop-[] ⟩⇒
                erase str u
                  T.[ T.consSubst (T.consSubst σ′ (loop str))
                        (loop str) ]                                    ∎⇒
            } }}}

      private opaque

        -- If r is non-zero, then the assumption related to t implies
        -- that there are terms t₁, t₂ and v₂ such that
        --
        -- * t [ σ ] reduces to the pair prodʷ p t₁ t₂,
        -- * t₂ is related to v₂,
        -- * if p is 𝟘, then erase str t T.[ σ′ ] reduces to v₂, and
        -- * if p is non-zero, then there is a term v₁ such that
        --   erase str t T.[ σ′ ] reduces to the pair T.prod v₁ v₂ and
        --   t₁ is related to v₁.

        r≢𝟘-lemma :
          r PE.≢ 𝟘 →
          ∃₃ λ t₁ t₂ v₂ →
          Δ ⊢ t [ σ ] ⇒* prodʷ p t₁ t₂ ∷
            (Σʷ p , q ▷ A ▹ B) [ σ ] ×
          t₂ ®⟨ l′ ⟩ v₂ ∷ B [ σ ⇑ ] [ t₁ ]₀ ×
          (p PE.≡ 𝟘 → erase str t T.[ σ′ ] T.⇒* v₂) ×
          (p PE.≢ 𝟘 →
           ∃ λ v₁ → erase str t T.[ σ′ ] T.⇒* T.prod v₁ v₂ ×
           t₁ ®⟨ l′ ⟩ v₁ ∷ A [ σ ])
        r≢𝟘-lemma r≢𝟘 =                                        $⟨ σ®σ′ ⟩

          σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ r ·ᶜ γ +ᶜ δ                       →⟨ (subsumption-®∷[]◂ λ x →

             (r ·ᶜ γ +ᶜ δ) ⟨ x ⟩ PE.≡ 𝟘                              →⟨ proj₁ ∘→ +ᶜ-positive-⟨⟩ (_ ·ᶜ γ) ⟩
             (r ·ᶜ γ) ⟨ x ⟩ PE.≡ 𝟘                                   →⟨ ·ᶜ-zero-product-⟨⟩ γ ⟩
             r PE.≡ 𝟘 ⊎ γ ⟨ x ⟩ PE.≡ 𝟘                               →⟨ (λ { (inj₁ r≡𝟘)    → ⊥-elim (r≢𝟘 r≡𝟘)
                                                                           ; (inj₂ γ⟨x⟩≡𝟘) → γ⟨x⟩≡𝟘
                                                                           }) ⟩
             γ ⟨ x ⟩ PE.≡ 𝟘                                          □) ⟩

          σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ γ                                 →⟨ ®∷→®∷◂ω non-trivial ∘→
                                                                  PE.subst (_®⟨_⟩_∷_◂_ _ _ _ _) (PE.cong ⌜_⌝ m≡𝟙ᵐ) ∘→
                                                                  ▸⊩ʳ∷⇔ .proj₁ (PE.subst₂ (_▸_⊩ʳ⟨_⟩_∷[_]_ _ _ _ _) (≢𝟘→ᵐ·≡ r≢𝟘) PE.refl ⊩ʳt)
                                                                    .proj₂ ∘→
                                                                  PE.subst₃ (_®_∷[_]_◂_ _ _) (PE.sym m≡𝟙ᵐ) PE.refl PE.refl ⟩
          t [ σ ] ®⟨ l′ ⟩ erase str t T.[ σ′ ] ∷
            (Σʷ p , q ▷ A ▹ B) [ σ ]                           →⟨ proj₂ ∘→ ®∷Σ⇔ .proj₁ ⟩

          (∃₃ λ t₁ t₂ v₂ →
           Δ ⊢ t [ σ ] ⇒* prodʷ p t₁ t₂ ∷
             (Σʷ p , q ▷ A ▹ B) [ σ ] ×
           t₂ ®⟨ l′ ⟩ v₂ ∷ B [ σ ⇑ ] [ t₁ ]₀ ×
           (p PE.≡ 𝟘 → erase str t T.[ σ′ ] T.⇒* v₂) ×
           (p PE.≢ 𝟘 →
            ∃ λ v₁ → erase str t T.[ σ′ ] T.⇒* T.prod v₁ v₂ ×
            t₁ ®⟨ l′ ⟩ v₁ ∷ A [ σ ]))                          □

      private opaque

        [sgSubst⇑][⇑][]₀≡ :
          ∀ v₁ {v₂} →
          v₁ T.[ T.sgSubst (loop str) T.⇑ ] T.[ σ′ T.⇑ ] T.[ v₂ ]₀ PE.≡
          v₁ T.[ T.consSubst (T.consSubst σ′ (loop str)) v₂ ]
        [sgSubst⇑][⇑][]₀≡ v₁ {v₂} =
          v₁ T.[ T.sgSubst (loop str) T.⇑ ] T.[ σ′ T.⇑ ] T.[ v₂ ]₀      ≡⟨ PE.cong T._[ _ ]₀ $ TP.subst-liftSubst-sgSubst v₁ ⟩

          v₁ T.[ σ′ T.⇑ T.⇑ ] T.[ T.sgSubst (loop str T.[ σ′ ]) T.⇑ ]
            T.[ v₂ ]₀                                                   ≡⟨ PE.cong (λ t → v₁ T.[ _ T.⇑ T.⇑ ] T.[ T.sgSubst t T.⇑ ] T.[ _ ]₀)
                                                                           loop-[] ⟩

          v₁ T.[ σ′ T.⇑ T.⇑ ] T.[ T.sgSubst (loop str) T.⇑ ] T.[ v₂ ]₀  ≡⟨ TP.singleSubstComp _ _ (v₁ T.[ _ ]) ⟩

          v₁ T.[ σ′ T.⇑ T.⇑ ] T.[ loop str , v₂ ]₁₀                     ≡⟨ TP.doubleSubstComp v₁ _ _ _ ⟩

          v₁ T.[ T.consSubst (T.consSubst σ′ (loop str)) v₂ ]           ∎

      private opaque

        -- The Prodrec-assumptions hold for σ and σ′ when r is
        -- non-zero and p is 𝟘:
        --
        -- * In this case t [ σ ] reduces to a pair prodʷ p t₁ t₂
        --   such that t₂ is related to v₂, where
        --   erase str t T.[ σ′ ] T.⇒* v₂.
        -- * Furthermore, because p is 𝟘, t₁ is related to anything.
        --
        -- The proof has two cases, one for non-strict applications
        -- and one for strict ones. In the strict case the fact that
        -- t₂ is related to v₂ implies that v₂ reduces to the
        -- value v₂′.

        r≢𝟘-p≡𝟘-lemma : r PE.≢ 𝟘 → p PE.≡ 𝟘 → Prodrec-assumptions σ σ′
        r≢𝟘-p≡𝟘-lemma r≢𝟘 PE.refl =
          case r≢𝟘-lemma r≢𝟘 of λ
            (t₁ , t₂ , v₂ , t[σ]⇒*t₁,t₂ , t₂®v₂ , hyp , _) →
          case hyp PE.refl of λ
            t[σ′]⇒*v₂ →
          case inversion-prod-Σ $
               syntacticRedTerm t[σ]⇒*t₁,t₂ .proj₂ .proj₂ of λ
            (_ , ⊢t₂ , _) →
          case PE.singleton str of λ where
            (T.non-strict , PE.refl) → record
              { t₁            = t₁
              ; t₂            = t₂
              ; v₁            = loop str
              ; v₂            = erase str t T.[ σ′ ]
              ; t₁®v₁         = ®∷◂𝟘 (·-zeroʳ _) (⊩A[σ] .proj₂)
              ; t₂®v₂         = ®∷→®∷◂ (®∷-⇐* (id ⊢t₂) t[σ′]⇒*v₂ t₂®v₂)
              ; t[σ]⇒*t₁,t₂   = t[σ]⇒*t₁,t₂
              ; ⇒*u[σ′,v₁,v₂] =
                  erase str (prodrec r 𝟘 q′ C t u) T.[ σ′ ]      ≡⟨ PE.cong T._[ _ ] $ prodrec-≢𝟘-𝟘 q′ C r≢𝟘 ⟩⇒

                  T.lam
                    (erase str u T.[ T.sgSubst (loop str) T.⇑ ]
                       T.[ σ′ T.⇑ ])
                    T.∘⟨ str ⟩
                  (erase str t T.[ σ′ ])                         ⇒⟨ T.β-red _ ⟩

                  erase str u T.[ T.sgSubst (loop str) T.⇑ ]
                    T.[ σ′ T.⇑ ] T.[ erase str t T.[ σ′ ] ]₀     ≡⟨ [sgSubst⇑][⇑][]₀≡ (erase _ u) ⟩⇒

                  erase str u
                    T.[ T.consSubst (T.consSubst σ′ (loop str))
                          (erase str t T.[ σ′ ]) ]               ∎⇒
              }
            (T.strict , PE.refl) →
              case reduces-to-value PE.refl t₂®v₂ of λ
                (v₂′ , v₂′-val , v₂⇒*v₂′) → record
              { t₁            = t₁
              ; t₂            = t₂
              ; v₁            = loop str
              ; v₂            = v₂′
              ; t₁®v₁         = ®∷◂𝟘 (·-zeroʳ _) (⊩A[σ] .proj₂)
              ; t₂®v₂         = ®∷→®∷◂ (®∷-⇒* v₂⇒*v₂′ t₂®v₂)
              ; t[σ]⇒*t₁,t₂   = t[σ]⇒*t₁,t₂
              ; ⇒*u[σ′,v₁,v₂] =
                  erase str (prodrec r 𝟘 q′ C t u) T.[ σ′ ]            ≡⟨ PE.cong T._[ _ ] $ prodrec-≢𝟘-𝟘 q′ C r≢𝟘 ⟩⇒

                  T.lam
                    (erase str u T.[ T.sgSubst (loop str) T.⇑ ]
                       T.[ σ′ T.⇑ ])
                    T.∘⟨ str ⟩
                  (erase str t T.[ σ′ ])                               ⇒*⟨ TP.app-subst*-arg T.lam t[σ′]⇒*v₂ ⟩

                  T.lam
                    (erase str u T.[ T.sgSubst (loop str) T.⇑ ]
                       T.[ σ′ T.⇑ ])
                    T.∘⟨ str ⟩
                  v₂                                                   ⇒*⟨ TP.app-subst*-arg T.lam v₂⇒*v₂′ ⟩

                  T.lam
                    (erase str u T.[ T.sgSubst (loop str) T.⇑ ]
                       T.[ σ′ T.⇑ ])
                    T.∘⟨ str ⟩
                  v₂′                                                  ⇒⟨ T.β-red v₂′-val ⟩

                  erase str u T.[ T.sgSubst (loop str) T.⇑ ]
                    T.[ σ′ T.⇑ ] T.[ v₂′ ]₀                            ≡⟨ [sgSubst⇑][⇑][]₀≡ (erase _ u) ⟩⇒

                  erase str u
                    T.[ T.consSubst (T.consSubst σ′ (loop str)) v₂′ ]  ∎⇒
              }

      private opaque

        -- The Prodrec-assumptions hold for σ and σ′ when both r and p
        -- are non-zero: in this case t [ σ ] reduces to a pair
        -- prodʷ p t₁ t₂ such that t₁ is related to v₁ and t₂ is
        -- related to v₂, where
        -- erase str t T.[ σ′ ] T.⇒* T.prod v₁ v₂.

        r≢𝟘-p≢𝟘-lemma : r PE.≢ 𝟘 → p PE.≢ 𝟘 → Prodrec-assumptions σ σ′
        r≢𝟘-p≢𝟘-lemma r≢𝟘 p≢𝟘 =
          case r≢𝟘-lemma r≢𝟘 of λ
            (t₁ , t₂ , v₂ , t[σ]⇒*t₁,t₂ , t₂®v₂ , _ , hyp) →
          case hyp p≢𝟘 of λ
            (v₁ , t[σ′]⇒*v₁,v₂ , t₁®v₁) → record
              { t₁            = t₁
              ; t₂            = t₂
              ; v₁            = v₁
              ; v₂            = v₂
              ; t₁®v₁         = ®∷→®∷◂ t₁®v₁
              ; t₂®v₂         = ®∷→®∷◂ t₂®v₂
              ; t[σ]⇒*t₁,t₂   = t[σ]⇒*t₁,t₂
              ; ⇒*u[σ′,v₁,v₂] =
                  erase str (prodrec r p q′ C t u) T.[ σ′ ]             ≡⟨ PE.cong T._[ _ ] $ prodrec-≢𝟘-≢𝟘 q′ C r≢𝟘 p≢𝟘 ⟩⇒

                  T.prodrec (erase str t) (erase str u) T.[ σ′ ]        ⇒*⟨ TP.prodrec-subst* t[σ′]⇒*v₁,v₂ ⟩

                  T.prodrec (T.prod v₁ v₂)
                    (erase str u T.[ σ′ T.⇑ T.⇑ ])                      ⇒⟨ T.prodrec-β ⟩

                  erase str u T.[ σ′ T.⇑ T.⇑ ] T.[ v₁ , v₂ ]₁₀          ≡⟨ TP.doubleSubstComp (erase _ u) _ _ _ ⟩⇒

                  erase str u T.[ T.consSubst (T.consSubst σ′ v₁) v₂ ]  ∎⇒
              }

      private opaque

        -- The Prodrec-assumptions hold for σ and σ′.

        prodrec-assumptions : Prodrec-assumptions σ σ′
        prodrec-assumptions = case is-𝟘? r of λ where
          (yes r≡𝟘) → r≡𝟘-lemma r≡𝟘
          (no r≢𝟘)  → case is-𝟘? p of λ where
            (yes p≡𝟘) → r≢𝟘-p≡𝟘-lemma r≢𝟘 p≡𝟘
            (no p≢𝟘)  → r≢𝟘-p≢𝟘-lemma r≢𝟘 p≢𝟘

      open Prodrec-assumptions prodrec-assumptions public

      private opaque

        ⊢C[σ⇑] : Δ ∙ (Σʷ p , q ▷ A ▹ B) [ σ ] ⊢ C [ σ ⇑ ]
        ⊢C[σ⇑] = escape $ ⊩ᵛ→⊩ˢ∷→⊩[⇑] ⊩C ⊩σ

      private opaque

        ⊢u[σ⇑⇑] :
          Δ ∙ A [ σ ] ∙ B [ σ ⇑ ] ⊢ u [ σ ⇑ ⇑ ] ∷
            C [ σ ⇑ ] [ prodʷ p (var x1) (var x0) ]↑²
        ⊢u[σ⇑⇑] =
          PE.subst (_⊢_∷_ _ _) (subst-β-prodrec C _) $
          escape-⊩∷ $ ⊩ᵛ∷→⊩ˢ∷→⊩[⇑⇑]∷ (fundamental-⊩ᵛ∷ ⊢u) ⊩σ

      private opaque

        C[σ⇑][t[σ]]≡C[σ⇑][t₁,t₂] :
          Δ ⊩⟨ l ⟩ C [ σ ⇑ ] [ t [ σ ] ]₀ ≡
            C [ σ ⇑ ] [ prodʷ p t₁ t₂ ]₀
        C[σ⇑][t[σ]]≡C[σ⇑][t₁,t₂] =
          ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ (refl-⊩ᵛ≡ ⊩C)
            (refl-⊩ˢ≡∷ ⊩σ)
            (reducible-⊩≡∷ (subset*Term t[σ]⇒*t₁,t₂))

      opaque

        ⇒*u[σ,t₁,t₂] :
          Δ ⊢ prodrec r p q′ C t u [ σ ] ⇒*
            u [ consSubst (consSubst σ t₁) t₂ ] ∷
            C [ σ ⇑ ] [ t [ σ ] ]₀
        ⇒*u[σ,t₁,t₂] =
          prodrec r p q′ C t u [ σ ] ∷ C [ σ ⇑ ] [ t [ σ ] ]₀  ⇒*⟨ prodrec-subst* ⊢C[σ⇑] t[σ]⇒*t₁,t₂ ⊢u[σ⇑⇑] ⟩∷
                                                                 ⟨ ≅-eq $ escape-⊩≡ C[σ⇑][t[σ]]≡C[σ⇑][t₁,t₂] ⟩⇒
          prodrec r p q′ (C [ σ ⇑ ]) (prodʷ p t₁ t₂)
            (u [ σ ⇑ ⇑ ]) ∷
            C [ σ ⇑ ] [ prodʷ p t₁ t₂ ]₀                       ⇒⟨ prodrec-β-⇒ ⊢C[σ⇑] ⊢t₁ ⊢t₂ ⊢u[σ⇑⇑] (⊢A,⊢B,ok .proj₂ .proj₂) ⟩∎∷≡

          u [ σ ⇑ ⇑ ] [ t₁ , t₂ ]₁₀                            ≡⟨ doubleSubstComp u _ _ _ ⟩

          u [ consSubst (consSubst σ t₁) t₂ ]                  ∎
          where
          open RR

      opaque

        C[1,0]↑²[σ,t₁,t₂]≡C[σ⇑][t[σ]] :
          Δ ⊩⟨ l ⟩
            C [ prodʷ p (var x1) (var x0) ]↑²
              [ consSubst (consSubst σ t₁) t₂ ] ≡
            C [ σ ⇑ ] [ t [ σ ] ]₀
        C[1,0]↑²[σ,t₁,t₂]≡C[σ⇑][t[σ]] =
          C [ prodʷ p (var x1) (var x0) ]↑²
            [ consSubst (consSubst σ t₁) t₂ ]  ≡˘⟨ substComp↑² C _ ⟩⊩≡

          C [ consSubst σ (prodʷ p t₁ t₂) ]    ≡˘⟨ singleSubstComp _ _ C ⟩⊩≡

          C [ σ ⇑ ] [ prodʷ p t₁ t₂ ]₀         ≡˘⟨ C[σ⇑][t[σ]]≡C[σ⇑][t₁,t₂] ⟩⊩∎

          C [ σ ⇑ ] [ t [ σ ] ]₀               ∎
