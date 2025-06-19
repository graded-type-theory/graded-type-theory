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
open import
  Definition.LogicalRelation.Fundamental.Reducibility.Restricted TR
open import Definition.LogicalRelation.Hidden TR
import Definition.LogicalRelation.Hidden.Restricted TR as R
open import Definition.LogicalRelation.Properties TR
open import Definition.LogicalRelation.Substitution TR
import Definition.LogicalRelation.Substitution.Introductions TR as I

open import Definition.Typed TR
open import Definition.Typed.Consequences.Admissible TR
open import Definition.Typed.Consequences.Inversion TR
open import Definition.Typed.Consequences.Reduction TR
open import Definition.Typed.Inversion TR
open import Definition.Typed.Properties TR
import Definition.Typed.Reasoning.Reduction TR as RR
open import Definition.Typed.Substitution TR
open import Definition.Typed.Syntactic TR
open import Definition.Typed.Well-formed TR

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M
open import Definition.Untyped.Whnf M type-variant

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
open import Tools.Nat
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum using (_⊎_; inj₁; inj₂)

private variable
  n o       : Nat
  Γ         : Con Term _
  σ         : Subst _ _
  σ′        : T.Subst _ _
  A B C t u : Term _
  γ δ       : Conₘ _
  p q q′ r  : M
  m         : Mode
  b         : BinderMode
  s         : Strength
  l         : Universe-level

------------------------------------------------------------------------
-- A lemma related to Π and Σ

opaque

  -- Validity of Π and Σ.

  ΠΣʳ : γ ▸ Γ ⊩ʳ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ∷[ m ∣ n ] U l
  ΠΣʳ =
    ▸⊩ʳ∷⇔ .proj₂ λ _ _ →
    ®∷→®∷◂ (®∷U⇔ .proj₂ (_ , ≤ᵘ-refl , Uᵣ (λ { PE.refl → T.refl })))

------------------------------------------------------------------------
-- Lemmas related to Π

opaque

  -- Validity of lam.

  lamʳ :
    Π-allowed p q →
    ts » Γ ∙ A ⊢ t ∷ B →
    γ ∙ ⌜ m ⌝ · p ▸ Γ ∙ A ⊩ʳ t ∷[ m ∣ n ] B →
    γ ▸ Γ ⊩ʳ lam p t ∷[ m ∣ n ] Π p , q ▷ A ▹ B
  lamʳ {m = 𝟘ᵐ} _ _ _ =
    ▸⊩ʳ∷[𝟘ᵐ]
  lamʳ {p} {Γ} {A} {t} {B} {γ} {m = 𝟙ᵐ} {n} ok ⊢t ⊩ʳt =
    ▸⊩ʳ∷⇔ .proj₂ λ {σ = σ} {σ′ = σ′} ⊩σ σ®σ′ →
    case fundamental-⊩ᵛ∷ ⊢t of λ
      (_ , ⊩t) →
    case wf-⊩ᵛ∷ ⊩t of λ
      ⊩B →
    case wf-∙-⊩ᵛ ⊩B of λ
      (_ , ⊩A) →

    ®∷→®∷◂ $
    ®∷Π⇔ .proj₂
      ( R.escape-⊩
          (⊩ᵛ→⊩ˢ∷→⊩[]
             (I.ΠΣᵛ (ΠΣⱼ (wf-⊢∷ ⊢t) ok) (emb-⊩ᵛ ≤ᵘ⊔ᵘʳ ⊩A)
                (emb-⊩ᵛ ≤ᵘ⊔ᵘˡ ⊩B))
             ⊩σ)
      , (λ { PE.refl → _ , T.refl })
      , λ t′ ⊢t′ →
          case reducible-⊩∷ ⊢t′ of λ
            (_ , ⊩t′) →
          case ⊩ˢ∷∙⇔′ .proj₂ ((_ , ⊩A) , (_ , ⊩t′) , ⊩σ) of λ
            ⊩σ,t′ →
          case redMany $
               β-red-⇒ (subst-⊢∷-⇑ ⊢t (escape-⊩ˢ∷ ⊩σ .proj₂)) ⊢t′
                 ok of λ
            lam-t[σ]∘t′⇒* →

            (λ { p≡𝟘@PE.refl →
                 case (case PE.singleton str of λ where
                   (T.non-strict , PE.refl) →
                     erase str (lam 𝟘 t) T.[ σ′ ]                        ≡⟨ PE.cong T._[ _ ] lam-𝟘-remove ⟩⇒
                     erase str t T.[ loop? str ]₀ T.[ σ′ ]               ≡⟨ TP.singleSubstLift (erase _ t) _ ⟩⇒
                     erase str t T.[ σ′ T.⇑ ] T.[ loop? str T.[ σ′ ] ]₀  ≡⟨ PE.cong (T._[_]₀ (erase _ t T.[ _ ])) $ loop?-[] _ ⟩⇒
                     erase str t T.[ σ′ T.⇑ ] T.[ loop? str ]₀           ∎⇒
                   (T.strict , PE.refl) →
                     (erase str (lam 𝟘 t) T.[ σ′ ]) T.∘⟨ str ⟩ loop? str  ≡⟨ PE.cong₃ T._∘⟨_⟩_ (PE.cong₂ T._[_] (lam-𝟘-keep t) PE.refl)
                                                                               PE.refl PE.refl ⟩⇒
                     (T.lam (erase str t) T.[ σ′ ]) T.∘⟨ str ⟩ loop? str  ⇒⟨ T.β-red T.↯ ⟩
                     erase str t T.[ σ′ T.⇑ ] T.[ loop? str ]₀            ∎⇒)
                 of λ
                   (lam-⌜t⌝[σ′]∘₀⇒* :
                    vs T.⊢ app-𝟘 str (erase str (lam 𝟘 t) T.[ σ′ ]) ⇒*
                    erase str t T.[ σ′ T.⇑ ] T.[ loop? str ]₀) →        $⟨ ®∷◂𝟘 (PE.trans (·-identityˡ _) (·-identityˡ _)) ⟩

                 t′ ® loop? str ∷ A [ σ ] ◂ 𝟙 · 𝟙 · 𝟘                   →⟨ (λ t′®loop? → ®∷[∣]∙◂∙⇔ .proj₂ (t′®loop? , σ®σ′)) ⟩

                 consSubst σ t′ ®
                   T.consSubst σ′ (loop? str) ∷[ 𝟙ᵐ ∣ n ] Γ ∙ A ◂
                   γ ∙ 𝟙 · 𝟘                                            →⟨ ▸⊩ʳ∷⇔ .proj₁ ⊩ʳt ⊩σ,t′ ⟩

                 t [ consSubst σ t′ ] ®
                   erase str t T.[ T.consSubst σ′ (loop? str) ] ∷
                   B [ consSubst σ t′ ] ◂ 𝟙                             →⟨ ®∷→®∷◂ω non-trivial ⟩

                 t [ consSubst σ t′ ] ®
                   erase str t T.[ T.consSubst σ′ (loop? str) ] ∷
                   B [ consSubst σ t′ ]                                 ≡⟨ PE.cong₃ _®_∷_ (PE.sym $ singleSubstComp _ _ t)
                                                                             (PE.sym $ TP.singleSubstComp _ _ (erase _ t))
                                                                             (PE.sym $ singleSubstComp _ _ B) ⟩→
                 t [ σ ⇑ ] [ t′ ]₀ ®
                   erase str t T.[ σ′ T.⇑ ] T.[ loop? str ]₀ ∷
                   B [ σ ⇑ ] [ t′ ]₀                                    →⟨ ®∷-⇐* lam-t[σ]∘t′⇒* lam-⌜t⌝[σ′]∘₀⇒* ⟩

                 (lam 𝟘 t [ σ ]) ∘⟨ 𝟘 ⟩ t′ ®
                   app-𝟘 str (erase str (lam 𝟘 t) T.[ σ′ ]) ∷
                   B [ σ ⇑ ] [ t′ ]₀                                    □ })

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
                  ∃ λ v″ → vs T.⊢ v′ ⇒* v″ ×
                  vs T.⊢ (T.lam (erase str t) T.[ σ′ ]) T.∘⟨ str ⟩ v′ ⇒*
                  erase str t T.[ T.liftSubst σ′ ] T.[ v″ ]₀) →
                                                                       $⟨ t′®v′ ⟩

               (t′ ® v′ ∷ A [ σ ])                                     →⟨ ®∷-⇒* v′⇒*v″ ⟩

               (t′ ® v″ ∷ A [ σ ])                                     →⟨ (λ t′®v″ → ®∷[∣]∙◂∙⇔ .proj₂ (®∷→®∷◂ t′®v″ , σ®σ′)) ⟩

               consSubst σ t′ ® T.consSubst σ′ v″ ∷[ 𝟙ᵐ ∣ n ] Γ ∙ A ◂
                 γ ∙ 𝟙 · p                                             →⟨ ▸⊩ʳ∷⇔ .proj₁ ⊩ʳt ⊩σ,t′ ⟩

               t [ consSubst σ t′ ] ®
                 erase str t T.[ T.consSubst σ′ v″ ] ∷
                 B [ consSubst σ t′ ] ◂ 𝟙                              →⟨ ®∷→®∷◂ω non-trivial ⟩

               t [ consSubst σ t′ ] ®
                 erase str t T.[ T.consSubst σ′ v″ ] ∷
                 B [ consSubst σ t′ ]                                  ≡⟨ PE.cong₃ _®_∷_ (PE.sym $ singleSubstComp _ _ t)
                                                                            (PE.sym $ TP.singleSubstComp _ _ (erase _ t))
                                                                            (PE.sym $ singleSubstComp _ _ B) ⟩→
               t [ σ ⇑ ] [ t′ ]₀ ®
                 erase str t T.[ σ′ T.⇑ ] T.[ v″ ]₀ ∷
                 B [ σ ⇑ ] [ t′ ]₀                                     →⟨ ®∷-⇐* lam-t[σ]∘t′⇒* lam-⌜t⌝[σ′]∘v′⇒* ⟩

               (lam p t [ σ ]) ∘⟨ p ⟩ t′ ®
                 (T.lam (erase str t) T.[ σ′ ]) T.∘⟨ str ⟩ v′ ∷
                 B [ σ ⇑ ] [ t′ ]₀                                     ≡⟨ PE.cong₂ (_®_∷_ _)
                                                                            (PE.cong (T._∘⟨ _ ⟩ _) $ PE.cong T._[ _ ] $ PE.sym $
                                                                             lam-≢𝟘 (str T.== T.non-strict) p≢𝟘)
                                                                            PE.refl ⟩→
               (lam p t [ σ ]) ∘⟨ p ⟩ t′ ®
                 (erase str (lam p t) T.[ σ′ ]) T.∘⟨ str ⟩ v′ ∷
                 B [ σ ⇑ ] [ t′ ]₀                                     □)
      )
    where
    open Graded.Erasure.Target.Reasoning

opaque

  -- Validity of _∘⟨_⟩_.

  ∘ʳ :
    ts » Γ ⊢ u ∷ A →
    γ ▸ Γ ⊩ʳ t ∷[ m ∣ n ] Π p , q ▷ A ▹ B →
    δ ▸ Γ ⊩ʳ u ∷[ m ᵐ· p ∣ n ] A →
    γ +ᶜ p ·ᶜ δ ▸ Γ ⊩ʳ t ∘⟨ p ⟩ u ∷[ m ∣ n ] B [ u ]₀
  ∘ʳ {m = 𝟘ᵐ} _ _ _ =
    ▸⊩ʳ∷[𝟘ᵐ]
  ∘ʳ {Γ} {u} {A} {γ} {t} {m = 𝟙ᵐ} {n} {p} {q} {B} {δ} ⊢u ⊩ʳt ⊩ʳu =
    ▸⊩ʳ∷⇔ .proj₂ λ {σ = σ} {σ′ = σ′} ⊩σ σ®σ′ →
    case
      (t ∘⟨ 𝟘 ⟩ u) [ σ ] ®
        app-𝟘 str (erase str t T.[ σ′ ]) ∷ B [ σ ⇑ ] [ u [ σ ] ]₀  ≡⟨ PE.cong (flip (_®_∷_ _) _) $ PE.sym $
                                                                      app-𝟘-[] (erase str t) ⟩→
      (t ∘⟨ 𝟘 ⟩ u) [ σ ] ®
        app-𝟘 str (erase str t) T.[ σ′ ] ∷ B [ σ ⇑ ] [ u [ σ ] ]₀  ≡⟨ PE.cong (flip (_®_∷_ _) _) $ PE.cong T._[ _ ] $ PE.sym
                                                                      ∘-𝟘 ⟩→
      (t ∘⟨ 𝟘 ⟩ u) [ σ ] ® erase str (t ∘⟨ 𝟘 ⟩ u) T.[ σ′ ] ∷
        B [ σ ⇑ ] [ u [ σ ] ]₀                                     □
    of λ
      𝟘-lemma →

    case
      (λ (p≢𝟘 : p PE.≢ 𝟘) →

         case PE.sym $ ≢𝟘→⌞⌟≡𝟙ᵐ p≢𝟘 of λ
           𝟙ᵐ≡⌞p⌟ →

         case                                        $⟨ σ®σ′ ⟩

           σ ® σ′ ∷[ 𝟙ᵐ ∣ n ] Γ ◂ γ +ᶜ p ·ᶜ δ        →⟨ (subsumption-®∷[∣]◂ λ x →

             (γ +ᶜ p ·ᶜ δ) ⟨ x ⟩ PE.≡ 𝟘                    →⟨ proj₂ ∘→ +ᶜ-positive-⟨⟩ γ ⟩
             (p ·ᶜ δ) ⟨ x ⟩ PE.≡ 𝟘                         →⟨ ·ᶜ-zero-product-⟨⟩ δ ⟩
             p PE.≡ 𝟘 ⊎ δ ⟨ x ⟩ PE.≡ 𝟘                     →⟨ (λ { (inj₁ p≡𝟘)    → ⊥-elim (p≢𝟘 p≡𝟘)
                                                                 ; (inj₂ δ⟨x⟩≡𝟘) → δ⟨x⟩≡𝟘
                                                                 }) ⟩
             δ ⟨ x ⟩ PE.≡ 𝟘                                □) ⟩

           σ ® σ′ ∷[ 𝟙ᵐ ∣ n ] Γ ◂ δ                  ≡⟨ PE.cong₄ (_®_∷[_∣_]_◂_ _ _) 𝟙ᵐ≡⌞p⌟ PE.refl PE.refl PE.refl ⟩→

           σ ® σ′ ∷[ ⌞ p ⌟ ∣ n ] Γ ◂ δ               →⟨ ▸⊩ʳ∷⇔ .proj₁ ⊩ʳu ⊩σ ⟩

           u [ σ ] ® erase str u T.[ σ′ ] ∷
             A [ σ ] ◂ ⌜ ⌞ p ⌟ ⌝                     →⟨ ®∷→®∷◂ω (non-trivial ∘→ PE.trans (PE.cong ⌜_⌝ 𝟙ᵐ≡⌞p⌟)) ⟩

           u [ σ ] ® erase str u T.[ σ′ ] ∷ A [ σ ]  □
         of λ
           u[σ]® →

         (u [ σ ] ® erase str u T.[ σ′ ] ∷ A [ σ ] →
          (t ∘⟨ p ⟩ u) [ σ ] ®
            (erase str t T.∘⟨ str ⟩ erase str u) T.[ σ′ ] ∷
            B [ σ ⇑ ] [ u [ σ ] ]₀)                          →⟨ _$ u[σ]® ⟩

         (t ∘⟨ p ⟩ u) [ σ ] ®
           (erase str t T.∘⟨ str ⟩ erase str u) T.[ σ′ ] ∷
           B [ σ ⇑ ] [ u [ σ ] ]₀                            ≡⟨ PE.cong (flip (_®_∷_ _) _) $ PE.cong T._[ _ ] $ PE.sym $
                                                                ∘-≢𝟘 p≢𝟘 ⟩→
         (t ∘⟨ p ⟩ u) [ σ ] ®
           erase str (t ∘⟨ p ⟩ u) T.[ σ′ ] ∷
           B [ σ ⇑ ] [ u [ σ ] ]₀                            □)
    of λ
      ≢𝟘-lemma →                                                $⟨ σ®σ′ ⟩

    σ ® σ′ ∷[ 𝟙ᵐ ∣ n ] Γ ◂ γ +ᶜ p ·ᶜ δ                          →⟨ subsumption-®∷[∣]◂ (λ _ → proj₁ ∘→ +ᶜ-positive-⟨⟩ γ) ⟩

    σ ® σ′ ∷[ 𝟙ᵐ ∣ n ] Γ ◂ γ                                    →⟨ ®∷→®∷◂ω non-trivial ∘→
                                                                   ▸⊩ʳ∷⇔ .proj₁ ⊩ʳt ⊩σ ⟩

    (t [ σ ] ® erase str t T.[ σ′ ] ∷ (Π p , q ▷ A ▹ B) [ σ ])  →⟨ (λ hyp →
                                                                      hyp _ $ R.escape-⊩∷ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ (fundamental-⊩ᵛ∷ ⊢u .proj₂) ⊩σ) ∘→
                                                                   proj₂ ∘→ proj₂ ∘→ ®∷Π⇔ .proj₁ ⟩
    (p PE.≡ 𝟘 →
     (t ∘⟨ 𝟘 ⟩ u) [ σ ] ® app-𝟘 str (erase str t T.[ σ′ ]) ∷
        B [ σ ⇑ ] [ u [ σ ] ]₀) ×
    (p PE.≢ 𝟘 →
     ∀ v′ → u [ σ ] ® v′ ∷ A [ σ ] →
     (t ∘⟨ p ⟩ u) [ σ ] ®
       (erase str t T.[ σ′ ]) T.∘⟨ str ⟩ v′ ∷
       B [ σ ⇑ ] [ u [ σ ] ]₀)                                  →⟨ (λ (≡𝟘→ , ≢𝟘→) →
                                                                      case is-𝟘? p of λ where
                                                                        (yes PE.refl) → 𝟘-lemma (≡𝟘→ PE.refl)
                                                                        (no p≢𝟘)      → ≢𝟘-lemma p≢𝟘 (≢𝟘→ p≢𝟘 _)) ⟩
    ((t ∘⟨ p ⟩ u) [ σ ] ® erase str (t ∘⟨ p ⟩ u) T.[ σ′ ] ∷
       B [ σ ⇑ ] [ u [ σ ] ]₀)                                  ≡⟨ PE.cong (_®_∷_ _ _) $ PE.sym $
                                                                   singleSubstLift B _ ⟩→
    ((t ∘⟨ p ⟩ u) [ σ ] ®
       erase str (t ∘⟨ p ⟩ u) T.[ σ′ ] ∷ B [ u ]₀ [ σ ])        →⟨ ®∷→®∷◂ ⟩

    (t ∘⟨ p ⟩ u) [ σ ] ®
      erase str (t ∘⟨ p ⟩ u) T.[ σ′ ] ∷ B [ u ]₀ [ σ ] ◂ 𝟙      □

------------------------------------------------------------------------
-- Lemmas related to Σ

opaque

  -- Validity of prod.

  prodʳ :
    (_⊕ᶜ_ : Conₘ o → Conₘ o → Conₘ o) →
    (∀ {x γ δ} →
     (γ ⊕ᶜ δ) ⟨ x ⟩ PE.≡ 𝟘 → γ ⟨ x ⟩ PE.≡ 𝟘 × δ ⟨ x ⟩ PE.≡ 𝟘) →
    Σ-allowed s p q →
    ts » Γ ∙ A ⊢ B →
    ts » Γ ⊢ t ∷ A →
    ts » Γ ⊢ u ∷ B [ t ]₀ →
    γ ▸ Γ ⊩ʳ t ∷[ m ᵐ· p ∣ n ] A →
    δ ▸ Γ ⊩ʳ u ∷[ m ∣ n ] B [ t ]₀ →
    ((p ·ᶜ γ) ⊕ᶜ δ) ▸ Γ ⊩ʳ prod s p t u ∷[ m ∣ n ] Σ⟨ s ⟩ p , q ▷ A ▹ B
  prodʳ {m = 𝟘ᵐ} _ _ _ _ _ _ _ _ =
    ▸⊩ʳ∷[𝟘ᵐ]
  prodʳ
    {s} {p} {Γ} {A} {B} {t} {u} {γ} {m = 𝟙ᵐ} {n} {δ}
    _⊕ᶜ_ ⊕ᶜ-positive-⟨⟩ ok ⊢B ⊢t ⊢u ⊩ʳt ⊩ʳu =
    ▸⊩ʳ∷⇔ .proj₂ λ {σ = σ} {σ′ = σ′} ⊩σ σ®σ′ →
    case fundamental-⊩ᵛ ⊢B of λ
      (_ , ⊩B) →
    case fundamental-⊩ᵛ∷ ⊢t of λ
      (_ , ⊩t) →
    case wf-⊩ᵛ∷ ⊩t of λ
      ⊩A →
    case escape-⊩ˢ∷ ⊩σ of λ
      (_ , ⊢σ) →

    case                                                       $⟨ σ®σ′ ⟩
      σ ® σ′ ∷[ 𝟙ᵐ ∣ n ] Γ ◂ ((p ·ᶜ γ) ⊕ᶜ δ)                   →⟨ subsumption-®∷[∣]◂ (λ _ → proj₂ ∘→ ⊕ᶜ-positive-⟨⟩) ⟩
      σ ® σ′ ∷[ 𝟙ᵐ ∣ n ] Γ ◂ δ                                 →⟨ ®∷→®∷◂ω non-trivial ∘→
                                                                  ▸⊩ʳ∷⇔ .proj₁ ⊩ʳu ⊩σ ⟩
      u [ σ ] ® erase str u T.[ σ′ ] ∷ B [ t ]₀ [ σ ]          ≡⟨ PE.cong (_®_∷_ _ _) (singleSubstLift B _) ⟩→
      u [ σ ] ® erase str u T.[ σ′ ] ∷ B [ σ ⇑ ] [ t [ σ ] ]₀  □
    of λ
      u[σ]® →

    case
      (λ p≢𝟘 →
         case PE.sym $ ≢𝟘→⌞⌟≡𝟙ᵐ p≢𝟘 of λ
           𝟙ᵐ≡⌞p⌟ →                                $⟨ σ®σ′ ⟩

         σ ® σ′ ∷[ 𝟙ᵐ ∣ n ] Γ ◂ ((p ·ᶜ γ) ⊕ᶜ δ)    →⟨ (subsumption-®∷[∣]◂ λ x →
           ((p ·ᶜ γ) ⊕ᶜ δ) ⟨ x ⟩ PE.≡ 𝟘                  →⟨ proj₁ ∘→ ⊕ᶜ-positive-⟨⟩ ⟩
           (p ·ᶜ γ) ⟨ x ⟩ PE.≡ 𝟘                         →⟨ ·ᶜ-zero-product-⟨⟩ γ ⟩
           p PE.≡ 𝟘 ⊎ γ ⟨ x ⟩ PE.≡ 𝟘                     →⟨ (λ { (inj₁ p≡𝟘)    → ⊥-elim (p≢𝟘 p≡𝟘)
                                                               ; (inj₂ γ⟨x⟩≡𝟘) → γ⟨x⟩≡𝟘
                                                               }) ⟩
           γ ⟨ x ⟩ PE.≡ 𝟘                                □) ⟩

         σ ® σ′ ∷[ 𝟙ᵐ ∣ n ] Γ ◂ γ                  ≡⟨ PE.cong₄ (_®_∷[_∣_]_◂_ _ _) 𝟙ᵐ≡⌞p⌟ PE.refl PE.refl PE.refl ⟩→

         σ ® σ′ ∷[ 𝟙ᵐ ᵐ· p ∣ n ] Γ ◂ γ             →⟨ ®∷→®∷◂ω (non-trivial ∘→ PE.trans (PE.cong ⌜_⌝ 𝟙ᵐ≡⌞p⌟)) ∘→
                                                      ▸⊩ʳ∷⇔ .proj₁ ⊩ʳt ⊩σ ⟩
         t [ σ ] ® erase str t T.[ σ′ ] ∷ A [ σ ]  □)
    of λ
      t[σ]® →

    case
      (∃ λ v₂ → vs T.⊢ erase str u T.[ σ′ ] ⇒* v₂ ×
       (p PE.≢ 𝟘 →
        ∃ λ v₁ → vs T.⊢ erase str t T.[ σ′ ] ⇒* v₁ ×
        vs T.⊢
          T.prod⟨ str ⟩ (erase str t T.[ σ′ ])
            (erase str u T.[ σ′ ]) ⇒*
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
      ( R.escape-⊩
          (⊩ᵛ→⊩ˢ∷→⊩[]
             (I.ΠΣᵛ (ΠΣⱼ ⊢B ok) (emb-⊩ᵛ ≤ᵘ⊔ᵘʳ ⊩A) (emb-⊩ᵛ ≤ᵘ⊔ᵘˡ ⊩B))
             ⊩σ)
      , t [ σ ] , u [ σ ] , v₂
      , (_⊢_⇒*_∷_.id $
         prodⱼ (subst-⊢-⇑ ⊢B ⊢σ) (subst-⊢∷ ⊢t ⊢σ)
           (PE.subst (_⊢_∷_ _ _) (singleSubstLift B _) $
            subst-⊢∷ ⊢u ⊢σ)
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
    where
    open Graded.Erasure.Target.Reasoning

opaque

  -- Validity of prodˢ.

  prodˢʳ :
    Σˢ-allowed p q →
    ts » Γ ∙ A ⊢ B →
    ts » Γ ⊢ t ∷ A →
    ts » Γ ⊢ u ∷ B [ t ]₀ →
    γ ▸ Γ ⊩ʳ t ∷[ m ᵐ· p ∣ n ] A →
    δ ▸ Γ ⊩ʳ u ∷[ m ∣ n ] B [ t ]₀ →
    p ·ᶜ γ ∧ᶜ δ ▸ Γ ⊩ʳ prodˢ p t u ∷[ m ∣ n ] Σˢ p , q ▷ A ▹ B
  prodˢʳ = prodʳ _∧ᶜ_ (λ {_} {γ = γ} → ∧ᶜ-positive-⟨⟩ γ)

opaque

  -- Validity of prodʷ.

  prodʷʳ :
    Σʷ-allowed p q →
    ts » Γ ∙ A ⊢ B →
    ts » Γ ⊢ t ∷ A →
    ts » Γ ⊢ u ∷ B [ t ]₀ →
    γ ▸ Γ ⊩ʳ t ∷[ m ᵐ· p ∣ n ] A →
    δ ▸ Γ ⊩ʳ u ∷[ m ∣ n ] B [ t ]₀ →
    p ·ᶜ γ +ᶜ δ ▸ Γ ⊩ʳ prodʷ p t u ∷[ m ∣ n ] Σʷ p , q ▷ A ▹ B
  prodʷʳ = prodʳ _+ᶜ_ (λ {_} {γ = γ} → +ᶜ-positive-⟨⟩ γ)

opaque

  -- Validity of fst.

  fstʳ :
    ts » Γ ⊢ t ∷ Σˢ p , q ▷ A ▹ B →
    γ ▸ Γ ⊩ʳ t ∷[ m ∣ n ] Σˢ p , q ▷ A ▹ B →
    γ ▸[ m ] fst p t →
    γ ▸ Γ ⊩ʳ fst p t ∷[ m ∣ n ] A
  fstʳ {m = 𝟘ᵐ} _ _ _ =
    ▸⊩ʳ∷[𝟘ᵐ]
  fstʳ {Γ} {t} {p} {q} {A} {B} {γ} {m = 𝟙ᵐ} {n} ⊢t ⊩ʳt ▸fst-t =
    ▸⊩ʳ∷⇔ .proj₂ λ {σ = σ} {σ′ = σ′} ⊩σ →
    case inversion-ΠΣ (wf-⊢∷ ⊢t) of λ
      (_ , ⊢B , ok) →
    case
      (λ p≡𝟘 →
         let open Tools.Reasoning.PartialOrder ≤-poset in
         𝟘≰𝟙 $ begin
           𝟘  ≡˘⟨ p≡𝟘 ⟩
           p  ≤⟨ InvUsageFst.mp-condition (inv-usage-fst ▸fst-t) PE.refl ⟩
           𝟙  ∎)
    of λ
      p≢𝟘 →

    σ ® σ′ ∷[ 𝟙ᵐ ∣ n ] Γ ◂ γ                                         →⟨ ®∷→®∷◂ω non-trivial ∘→
                                                                        ▸⊩ʳ∷⇔ .proj₁ ⊩ʳt ⊩σ ⟩

    (t [ σ ] ® erase str t T.[ σ′ ] ∷ (Σˢ p , q ▷ A ▹ B) [ σ ])      →⟨ proj₂ ∘→ ®∷Σω⇔ p≢𝟘 .proj₁ ⟩

    (∃₄ λ t₁ t₂ v₁ v₂ →
     ts » Δ ⊢ t [ σ ] ⇒* prodˢ p t₁ t₂ ∷ (Σˢ p , q ▷ A ▹ B) [ σ ] ×
     vs T.⊢ erase str t T.[ σ′ ] ⇒* T.prod v₁ v₂ ×
     t₁ ® v₁ ∷ A [ σ ] ×
     t₂ ® v₂ ∷ B [ σ ⇑ ] [ t₁ ]₀)                                    →⟨ (λ (t₁ , t₂ , v₁ , v₂ ,
                                                                            t[σ]⇒*t₁,t₂ , t[σ′]⇒*v₂,v₂ , t₁®v₁ , _) →
                                                                           case inversion-prod-Σ $
                                                                                syntacticRedTerm t[σ]⇒*t₁,t₂ .proj₂ .proj₂ of λ
                                                                             (⊢t₁ , ⊢t₂ , _) →
                                                                           ®∷-⇐*
                                                                             (let open RR in
       fst p (t [ σ ])                                                          ⇒*⟨ fst-subst* t[σ]⇒*t₁,t₂ ⟩
       fst p (prodˢ p t₁ t₂)                                                    ⇒⟨ Σ-β₁-⇒ (subst-⊢-⇑ ⊢B (escape-⊩ˢ∷ ⊩σ .proj₂)) ⊢t₁ ⊢t₂ ok ⟩∎
       t₁                                                                       ∎)
                                                                             (let open Graded.Erasure.Target.Reasoning in
       T.fst (erase str t T.[ σ′ ])                                             ⇒*⟨ TP.fst-subst* t[σ′]⇒*v₂,v₂ ⟩
       T.fst (T.prod v₁ v₂)                                                     ⇒⟨ T.Σ-β₁ ⟩
       v₁                                                                       ∎⇒)
                                                                             t₁®v₁) ⟩

    (fst p t [ σ ] ® T.fst (erase str t) T.[ σ′ ] ∷ A [ σ ])         ≡⟨ PE.cong₂ (_®_∷_ _) (PE.cong T._[ _ ] $ PE.sym $ fst-≢𝟘 p≢𝟘) PE.refl ⟩→

    (fst p t [ σ ] ® erase str (fst p t) T.[ σ′ ] ∷ A [ σ ])         →⟨ ®∷→®∷◂ ⟩

    fst p t [ σ ] ® erase str (fst p t) T.[ σ′ ] ∷ A [ σ ] ◂ 𝟙       □

opaque

  -- Validity of snd.

  sndʳ :
    ts » Γ ⊢ t ∷ Σˢ p , q ▷ A ▹ B →
    γ ▸ Γ ⊩ʳ t ∷[ m ∣ n ] Σˢ p , q ▷ A ▹ B →
    γ ▸ Γ ⊩ʳ snd p t ∷[ m ∣ n ] B [ fst p t ]₀
  sndʳ {m = 𝟘ᵐ} _ _ =
    ▸⊩ʳ∷[𝟘ᵐ]
  sndʳ {Γ} {t} {p} {q} {A} {B} {γ} {m = 𝟙ᵐ} {n} ⊢t ⊩ʳt =
    ▸⊩ʳ∷⇔ .proj₂ λ {σ = σ} {σ′ = σ′} ⊩σ →
    case I.⊩ᵛΠΣ→ (wf-⊩ᵛ∷ $ fundamental-⊩ᵛ∷ ⊢t .proj₂) of λ
      (_ , _ , ⊩B) →
    case inversion-ΠΣ (wf-⊢∷ ⊢t) of λ
      (_ , ⊢B , ok) →
    case subst-⊢-⇑ ⊢B (escape-⊩ˢ∷ ⊩σ .proj₂) of λ
      ⊢B[σ⇑] →

    σ ® σ′ ∷[ 𝟙ᵐ ∣ n ] Γ ◂ γ                                         →⟨ ®∷→®∷◂ω non-trivial ∘→
                                                                        ▸⊩ʳ∷⇔ .proj₁ ⊩ʳt ⊩σ ⟩

    (t [ σ ] ® erase str t T.[ σ′ ] ∷ (Σˢ p , q ▷ A ▹ B) [ σ ])      →⟨ proj₂ ∘→ ®∷Σ⇔ .proj₁ ⟩

    (∃₃ λ t₁ t₂ v₂ →
     ts » Δ ⊢ t [ σ ] ⇒* prodˢ p t₁ t₂ ∷ (Σˢ p , q ▷ A ▹ B) [ σ ] ×
     t₂ ® v₂ ∷ B [ σ ⇑ ] [ t₁ ]₀ ×
     (p PE.≡ 𝟘 → vs T.⊢ erase str t T.[ σ′ ] ⇒* v₂) ×
     (p PE.≢ 𝟘 →
      ∃ λ v₁ → vs T.⊢ erase str t T.[ σ′ ] ⇒* T.prod v₁ v₂ ×
      t₁ ® v₁ ∷ A [ σ ]))                                            →⟨ (λ (t₁ , t₂ , v₂ , t[σ]⇒*t₁,t₂ , t₂®v₂ , 𝟘-hyp , ≢𝟘-hyp) →
                                                                           case inversion-prod-Σ $
                                                                                syntacticRedTerm t[σ]⇒*t₁,t₂ .proj₂ .proj₂ of λ
                                                                             (⊢t₁ , ⊢t₂ , _) →
                                                                           ®∷-⇐*
                                                                             (let open RR in
      snd p (t [ σ ])       ∷ B [ σ ⇑ ] [ fst p (t [ σ ]) ]₀                    ⇒*⟨ snd-subst* t[σ]⇒*t₁,t₂ ⟩∷
                                                                                  ⟨ subst-⊢≡ (refl ⊢B[σ⇑]) $
                                                                                    ⊢ˢʷ≡∷-sgSubst (subset*Term $ fst-subst* t[σ]⇒*t₁,t₂) ⟩⇒
      snd p (prodˢ p t₁ t₂) ∷ B [ σ ⇑ ] [ fst p (prodˢ p t₁ t₂) ]₀              ⇒⟨ Σ-β₂-⇒ ⊢B[σ⇑] ⊢t₁ ⊢t₂ ok ⟩∎∷
      t₂                                                                        ∎)
                                                                             (let open Graded.Erasure.Target.Reasoning in
                                                                              case is-𝟘? p of λ {
                                                                                (no p≢𝟘) →
                                                                                  case ≢𝟘-hyp p≢𝟘 of λ
                                                                                    (v₁ , t[σ′]⇒*v₁,v₂ , _) →
      erase str (snd p t) T.[ σ′ ]                                                ≡⟨ PE.cong T._[ _ ] $ snd-ω p≢𝟘 ⟩⇒
      T.snd (erase str t T.[ σ′ ])                                                ⇒*⟨ TP.snd-subst* t[σ′]⇒*v₁,v₂ ⟩
      T.snd (T.prod v₁ v₂)                                                        ⇒⟨ T.Σ-β₂ ⟩
      v₂                                                                          ∎⇒;

                                                                                (yes PE.refl) →
      erase str (snd 𝟘 t) T.[ σ′ ]                                                ≡⟨ PE.cong T._[ _ ] $ snd-𝟘 PE.refl ⟩⇒
      erase str t T.[ σ′ ]                                                        ⇒*⟨ 𝟘-hyp PE.refl ⟩
      v₂                                                                          ∎⇒ }) $
                                                                           conv-®∷
                                                                             (let open RR in
                                                                              R.⊩≡→ $
                                                                              ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ (refl-⊩ᵛ≡ ⊩B) (refl-⊩ˢ≡∷ ⊩σ) $
                                                                              R.sym-⊩≡∷ $ proj₂ $ reducible-⊩≡∷ $ subset*Term (
      fst p (t [ σ ])                                                           ⇒*⟨ fst-subst* t[σ]⇒*t₁,t₂ ⟩
      fst p (prodˢ p t₁ t₂)                                                     ⇒⟨ Σ-β₁-⇒ ⊢B[σ⇑] ⊢t₁ ⊢t₂ ok ⟩∎
      t₁                                                                        ∎))
                                                                             t₂®v₂) ⟩
    (snd p t [ σ ] ® erase str (snd p t) T.[ σ′ ] ∷
       B [ σ ⇑ ] [ fst p t [ σ ] ]₀)                                 ≡⟨ PE.cong (_®_∷_ _ _) $ PE.sym $
                                                                        singleSubstLift B _ ⟩→
    (snd p t [ σ ] ® erase str (snd p t) T.[ σ′ ] ∷
       B [ fst p t ]₀ [ σ ])                                         →⟨ ®∷→®∷◂ ⟩

    snd p t [ σ ] ® erase str (snd p t) T.[ σ′ ] ∷
      B [ fst p t ]₀ [ σ ] ◂ 𝟙                                       □

opaque

  -- Validity of prodrec.

  prodrecʳ :
    {Γ : Con Term o} →
    ts » Γ ∙ Σʷ p , q ▷ A ▹ B ⊢ C →
    ts » Γ ⊢ t ∷ Σʷ p , q ▷ A ▹ B →
    ts » Γ ∙ A ∙ B ⊢ u ∷ C [ prodʷ p (var x1) (var x0) ]↑² →
    γ ▸ Γ ⊩ʳ t ∷[ m ᵐ· r ∣ n ] Σʷ p , q ▷ A ▹ B →
    δ ∙ ⌜ m ⌝ · r · p ∙ ⌜ m ⌝ · r ▸ Γ ∙ A ∙ B ⊩ʳ u ∷[ m ∣ n ]
      C [ prodʷ p (var x1) (var x0) ]↑² →
    (r PE.≡ 𝟘 → Empty-con Δ × Transparent ts) →
    r ·ᶜ γ +ᶜ δ ▸ Γ ⊩ʳ prodrec r p q′ C t u ∷[ m ∣ n ] C [ t ]₀
  prodrecʳ {m = 𝟘ᵐ} _ _ _ _ _ _ =
    ▸⊩ʳ∷[𝟘ᵐ]
  prodrecʳ
    {o} {p} {q} {A} {B} {C} {t} {u} {γ} {m = 𝟙ᵐ} {r} {n} {δ}
    {q′} {Γ} ⊢C ⊢t ⊢u ⊩ʳt ⊩ʳu r≡𝟘→ε =
    ▸⊩ʳ∷⇔ .proj₂ λ {σ = σ} {σ′ = σ′} ⊩σ σ®σ′ →
    let open Lemmas ⊩σ σ®σ′ in                                 $⟨ σ®σ′ ⟩

    σ ® σ′ ∷[ 𝟙ᵐ ∣ n ] Γ ◂ r ·ᶜ γ +ᶜ δ                         →⟨ subsumption-®∷[∣]◂ (λ _ → proj₂ ∘→ +ᶜ-positive-⟨⟩ (_ ·ᶜ γ)) ⟩

    σ ® σ′ ∷[ 𝟙ᵐ ∣ n ] Γ ◂ δ                                   →⟨ (λ σ®σ′ → ®∷[∣]∙◂∙⇔ .proj₂ (t₂®v₂′ , ®∷[∣]∙◂∙⇔ .proj₂ (t₁®v₁′ , σ®σ′))) ⟩

    consSubst (consSubst σ t₁) t₂ ®
      T.consSubst (T.consSubst σ′ v₁) v₂ ∷[ 𝟙ᵐ ∣ n ]
      Γ ∙ A ∙ B ◂ δ ∙ 𝟙 · r · p ∙ 𝟙 · r                        →⟨ ®∷→®∷◂ω non-trivial ∘→
                                                                  ▸⊩ʳ∷⇔ .proj₁ ⊩ʳu
                                                                    (⊩ˢ∷∙⇔′ .proj₂
                                                                       ( ⊩B
                                                                       , ( _
                                                                         , (proj₂ $ reducible-⊩∷ $
                                                                            PE.subst (_⊢_∷_ _ _) (singleSubstComp _ _ B) ⊢t₂)
                                                                         )
                                                                       , ⊩ˢ∷∙⇔′ .proj₂ (⊩A , (_ , reducible-⊩∷ ⊢t₁ .proj₂) , ⊩σ)
                                                                       )) ⟩
    (u [ consSubst (consSubst σ t₁) t₂ ] ®
       erase str u T.[ T.consSubst (T.consSubst σ′ v₁) v₂ ] ∷
       C [ prodʷ p (var x1) (var x0) ]↑²
         [ consSubst (consSubst σ t₁) t₂ ])                    →⟨ conv-®∷ C[1,0]↑²[σ,t₁,t₂]≡C[σ⇑][t[σ]] ⟩

    (u [ consSubst (consSubst σ t₁) t₂ ] ®
       erase str u T.[ T.consSubst (T.consSubst σ′ v₁) v₂ ] ∷
       C [ σ ⇑ ] [ t [ σ ] ]₀)                                 →⟨ ®∷-⇐* ⇒*u[σ,t₁,t₂] ⇒*u[σ′,v₁,v₂] ⟩

    (prodrec r p q′ C t u [ σ ] ®
       erase str (prodrec r p q′ C t u) T.[ σ′ ] ∷
       C [ σ ⇑ ] [ t [ σ ] ]₀)                                 →⟨ ®∷→®∷◂ ∘→
                                                                  PE.subst (_®_∷_ _ _) (PE.sym $ singleSubstLift C _) ⟩
    prodrec r p q′ C t u [ σ ] ®
      erase str (prodrec r p q′ C t u) T.[ σ′ ] ∷
      C [ t ]₀ [ σ ] ◂ 𝟙                                       □
    where
    open Tools.Reasoning.PropositionalEquality

    opaque

      ⊢A,⊢B : ts » Γ ⊢ A × ts » Γ ∙ A ⊢ B
      ⊢A,⊢B =
        Σ.map idᶠ proj₁ $
        inversion-ΠΣ $ syntacticTerm ⊢t

    opaque

      ⊩A : ∃ λ l → ts » Γ ⊩ᵛ⟨ l ⟩ A
      ⊩A = fundamental-⊩ᵛ (⊢A,⊢B .proj₁)

    opaque

      ⊩B : ∃ λ l → ts » Γ ∙ A ⊩ᵛ⟨ l ⟩ B
      ⊩B = fundamental-⊩ᵛ (⊢A,⊢B .proj₂)

    -- Some assumptions that are used in the proof.

    record Prodrec-assumptions
             (σ : Subst k o) (σ′ : T.Subst k o) : Set a where
      no-eta-equality
      field
        t₁ t₂         : Term k
        v₁ v₂         : T.Term k
        t₁®v₁         : t₁ ® v₁ ∷ A [ σ ] ◂ r · p
        t₂®v₂         : t₂ ® v₂ ∷ B [ σ ⇑ ] [ t₁ ]₀ ◂ r
        t[σ]⇒*t₁,t₂   : ts » Δ ⊢ t [ σ ] ⇒* prodʷ p t₁ t₂ ∷
                          (Σʷ p , q ▷ A ▹ B) [ σ ]
        ⇒*u[σ′,v₁,v₂] : vs T.⊢
                          erase str (prodrec r p q′ C t u) T.[ σ′ ] ⇒*
                          erase str u
                            T.[ T.consSubst (T.consSubst σ′ v₁) v₂ ]

      opaque

        ⊢t₁,⊢t₂ :
          ts » Δ ⊢ t₁ ∷ A [ σ ] × ts » Δ ⊢ t₂ ∷ B [ σ ⇑ ] [ t₁ ]₀
        ⊢t₁,⊢t₂ =
          Σ.map idᶠ proj₁ $
          inversion-prod-Σ $
          syntacticEqTerm (subset*Term t[σ]⇒*t₁,t₂) .proj₂ .proj₂

      opaque

        ⊢t₁ : ts » Δ ⊢ t₁ ∷ A [ σ ]
        ⊢t₁ = ⊢t₁,⊢t₂ .proj₁

      opaque

        ⊢t₂ : ts » Δ ⊢ t₂ ∷ B [ σ ⇑ ] [ t₁ ]₀
        ⊢t₂ = ⊢t₁,⊢t₂ .proj₂

      opaque

        t₁®v₁′ : t₁ ® v₁ ∷ A [ σ ] ◂ 𝟙 · 𝟙 · r · p
        t₁®v₁′ =
          PE.subst (_®_∷_◂_ _ _ _)
            (r · p          ≡˘⟨ ·-identityˡ _ ⟩
             𝟙 · r · p      ≡˘⟨ ·-identityˡ _ ⟩
             𝟙 · 𝟙 · r · p  ∎)
            t₁®v₁

      opaque

        t₂®v₂′ : t₂ ® v₂ ∷ B [ consSubst σ t₁ ] ◂ 𝟙 · 𝟙 · r
        t₂®v₂′ =
          PE.subst₂ (_®_∷_◂_ _ _) (singleSubstComp _ _ B)
            (r          ≡˘⟨ ·-identityˡ _ ⟩
             𝟙 · r      ≡˘⟨ ·-identityˡ _ ⟩
             𝟙 · 𝟙 · r  ∎)
            t₂®v₂

    module Lemmas
      (⊩σ   : ts » Δ ⊩ˢ σ ∷ Γ)
      (σ®σ′ : σ ® σ′ ∷[ 𝟙ᵐ ∣ n ] Γ ◂ r ·ᶜ γ +ᶜ δ)
      where

      open Graded.Erasure.Target.Reasoning

      private opaque

        ⊢σ : ts » Δ ⊢ˢʷ σ ∷ Γ
        ⊢σ = escape-⊩ˢ∷ ⊩σ .proj₂

      private opaque

        -- The Prodrec-assumptions hold for σ and σ′ when r is 𝟘:
        --
        -- * In this case the context is empty, so t [ σ ] must reduce
        --   to a pair.
        -- * Furthermore, because r is 𝟘, the components of the pair
        --   are related to anything.

        r≡𝟘-lemma : r PE.≡ 𝟘 → Prodrec-assumptions σ σ′
        r≡𝟘-lemma PE.refl =
          case r≡𝟘→ε PE.refl of λ {
            (ε , tr) →
          case red-Σ (subst-⊢∷ ⊢t ⊢σ) of λ {
            (_ , ne n , _) →
              ⊥-elim $ glass-closed-no-ne $
              PE.subst (flip (Neutral _) _) tr n;
            (_ , prodₙ {t = t₁} {u = t₂} , t[σ]⇒*t₁,t₂) →
          case inversion-prod-Σ $
               wf-⊢≡∷ (subset*Term t[σ]⇒*t₁,t₂) .proj₂ .proj₂ of λ {
            (_ , _ , PE.refl , PE.refl , _) →
          record
            { t₁            = t₁
            ; t₂            = t₂
            ; v₁            = loop str
            ; v₂            = loop str
            ; t₁®v₁         = ®∷◂𝟘 (·-zeroˡ _)
            ; t₂®v₂         = ®∷◂𝟘 PE.refl
            ; t[σ]⇒*t₁,t₂   = t[σ]⇒*t₁,t₂
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
          ts » Δ ⊢ t [ σ ] ⇒* prodʷ p t₁ t₂ ∷
            (Σʷ p , q ▷ A ▹ B) [ σ ] ×
          t₂ ® v₂ ∷ B [ σ ⇑ ] [ t₁ ]₀ ×
          (p PE.≡ 𝟘 → vs T.⊢ erase str t T.[ σ′ ] ⇒* v₂) ×
          (p PE.≢ 𝟘 →
           ∃ λ v₁ → vs T.⊢ erase str t T.[ σ′ ] ⇒* T.prod v₁ v₂ ×
           t₁ ® v₁ ∷ A [ σ ])
        r≢𝟘-lemma r≢𝟘 =                                              $⟨ σ®σ′ ⟩

          σ ® σ′ ∷[ 𝟙ᵐ ∣ n ] Γ ◂ r ·ᶜ γ +ᶜ δ                         →⟨ (subsumption-®∷[∣]◂ λ x →

             (r ·ᶜ γ +ᶜ δ) ⟨ x ⟩ PE.≡ 𝟘                                    →⟨ proj₁ ∘→ +ᶜ-positive-⟨⟩ (_ ·ᶜ γ) ⟩
             (r ·ᶜ γ) ⟨ x ⟩ PE.≡ 𝟘                                         →⟨ ·ᶜ-zero-product-⟨⟩ γ ⟩
             r PE.≡ 𝟘 ⊎ γ ⟨ x ⟩ PE.≡ 𝟘                                     →⟨ (λ { (inj₁ r≡𝟘)    → ⊥-elim (r≢𝟘 r≡𝟘)
                                                                                 ; (inj₂ γ⟨x⟩≡𝟘) → γ⟨x⟩≡𝟘
                                                                                 }) ⟩
             γ ⟨ x ⟩ PE.≡ 𝟘                                                □) ⟩

          σ ® σ′ ∷[ 𝟙ᵐ ∣ n ] Γ ◂ γ                                   →⟨ ®∷→®∷◂ω non-trivial ∘→
                                                                        ▸⊩ʳ∷⇔ .proj₁
                                                                          (PE.subst₃ (_▸_⊩ʳ_∷[_∣_]_ _ _ _) (≢𝟘→ᵐ·≡ r≢𝟘) PE.refl PE.refl ⊩ʳt) ⊩σ ⟩
          t [ σ ] ® erase str t T.[ σ′ ] ∷ (Σʷ p , q ▷ A ▹ B) [ σ ]  →⟨ proj₂ ∘→ ®∷Σ⇔ .proj₁ ⟩

          (∃₃ λ t₁ t₂ v₂ →
           ts » Δ ⊢ t [ σ ] ⇒* prodʷ p t₁ t₂ ∷
             (Σʷ p , q ▷ A ▹ B) [ σ ] ×
           t₂ ® v₂ ∷ B [ σ ⇑ ] [ t₁ ]₀ ×
           (p PE.≡ 𝟘 → vs T.⊢ erase str t T.[ σ′ ] ⇒* v₂) ×
           (p PE.≢ 𝟘 →
            ∃ λ v₁ → vs T.⊢ erase str t T.[ σ′ ] ⇒* T.prod v₁ v₂ ×
            t₁ ® v₁ ∷ A [ σ ]))                                      □

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
              ; t₁®v₁         = ®∷◂𝟘 (·-zeroʳ _)
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
              ; t₁®v₁         = ®∷◂𝟘 (·-zeroʳ _)
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

      private opaque mutual

        l′ : Universe-level
        l′ = _

        ⊩C : ts » Γ ∙ Σʷ p , q ▷ A ▹ B ⊩ᵛ⟨ l′ ⟩ C
        ⊩C = fundamental-⊩ᵛ ⊢C .proj₂

      private opaque

        ⊢C[σ⇑] : ts » Δ ∙ (Σʷ p , q ▷ A ▹ B) [ σ ] ⊢ C [ σ ⇑ ]
        ⊢C[σ⇑] = subst-⊢-⇑ ⊢C ⊢σ

      private opaque

        ⊢u[σ⇑⇑] :
          ts » Δ ∙ A [ σ ] ∙ B [ σ ⇑ ] ⊢ u [ σ ⇑ ⇑ ] ∷
            C [ σ ⇑ ] [ prodʷ p (var x1) (var x0) ]↑²
        ⊢u[σ⇑⇑] =
          PE.subst (_⊢_∷_ _ _) (subst-β-prodrec C _) $
          subst-⊢∷-⇑ ⊢u ⊢σ

      private opaque

        C[σ⇑][t[σ]]≡C[σ⇑][t₁,t₂] :
          ts » Δ ⊩⟨ l′ ⟩ C [ σ ⇑ ] [ t [ σ ] ]₀ ≡
            C [ σ ⇑ ] [ prodʷ p t₁ t₂ ]₀
        C[σ⇑][t[σ]]≡C[σ⇑][t₁,t₂] =
          R.⊩≡→ $
          ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ (refl-⊩ᵛ≡ ⊩C)
            (refl-⊩ˢ≡∷ ⊩σ)
            (reducible-⊩≡∷ (subset*Term t[σ]⇒*t₁,t₂) .proj₂)

      opaque

        ⇒*u[σ,t₁,t₂] :
          ts » Δ ⊢ prodrec r p q′ C t u [ σ ] ⇒*
            u [ consSubst (consSubst σ t₁) t₂ ] ∷
            C [ σ ⇑ ] [ t [ σ ] ]₀
        ⇒*u[σ,t₁,t₂] =
          prodrec r p q′ C t u [ σ ] ∷ C [ σ ⇑ ] [ t [ σ ] ]₀  ⇒*⟨ prodrec-subst* ⊢C[σ⇑] t[σ]⇒*t₁,t₂ ⊢u[σ⇑⇑] ⟩∷
                                                                 ⟨ ≅-eq $ escape-⊩≡ C[σ⇑][t[σ]]≡C[σ⇑][t₁,t₂] ⟩⇒
          prodrec r p q′ (C [ σ ⇑ ]) (prodʷ p t₁ t₂)
            (u [ σ ⇑ ⇑ ]) ∷
            C [ σ ⇑ ] [ prodʷ p t₁ t₂ ]₀                       ⇒⟨ prodrec-β-⇒ ⊢C[σ⇑] ⊢t₁ ⊢t₂ ⊢u[σ⇑⇑] ⟩∎∷≡

          u [ σ ⇑ ⇑ ] [ t₁ , t₂ ]₁₀                            ≡⟨ doubleSubstComp u _ _ _ ⟩

          u [ consSubst (consSubst σ t₁) t₂ ]                  ∎
          where
          open RR

      opaque

        C[1,0]↑²[σ,t₁,t₂]≡C[σ⇑][t[σ]] :
          ts » Δ ⊩⟨ l′ ⟩
            C [ prodʷ p (var x1) (var x0) ]↑²
              [ consSubst (consSubst σ t₁) t₂ ] ≡
            C [ σ ⇑ ] [ t [ σ ] ]₀
        C[1,0]↑²[σ,t₁,t₂]≡C[σ⇑][t[σ]] =
          C [ prodʷ p (var x1) (var x0) ]↑²
            [ consSubst (consSubst σ t₁) t₂ ]  ≡˘⟨ substComp↑² C _ ⟩⊩≡

          C [ consSubst σ (prodʷ p t₁ t₂) ]    ≡˘⟨ singleSubstComp _ _ C ⟩⊩≡

          C [ σ ⇑ ] [ prodʷ p t₁ t₂ ]₀         ≡˘⟨ C[σ⇑][t[σ]]≡C[σ⇑][t₁,t₂] ⟩⊩∎

          C [ σ ⇑ ] [ t [ σ ] ]₀               ∎
