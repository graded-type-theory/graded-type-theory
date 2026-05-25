------------------------------------------------------------------------
-- Validity for quotient types
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Erasure.LogicalRelation.Assumptions
open import Graded.Modality
import Graded.Mode.Instances.Zero-one
open import Graded.Mode.Instances.Zero-one.Variant
open import Graded.Usage.Restrictions

module Graded.Erasure.LogicalRelation.Fundamental.Quotient
  {a} {M : Set a}
  {𝕄 : Modality M}
  (open Modality 𝕄)
  {R : Type-restrictions 𝕄}
  {variant : Mode-variant 𝕄}
  (open Graded.Mode.Instances.Zero-one variant)
  (UR : Usage-restrictions 𝕄 Zero-one-isMode)
  (as : Assumptions R)
  ⦃ 𝟘-well-behaved : Has-well-behaved-zero M 𝕄 ⦄
  where

open Assumptions as
open Has-well-behaved-zero 𝟘-well-behaved
open Usage-restrictions UR

open import Definition.Typed R
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Reasoning.Type R
open import Definition.Typed.Substitution R
open import Definition.Typed.Well-formed R

open import Definition.Untyped M
open import Definition.Untyped.Properties M
open import Definition.Untyped.Quotient 𝕄

open import Graded.Context 𝕄
open import Graded.Context.Properties.Has-well-behaved-zero 𝕄
open import Graded.Erasure.Extraction 𝕄
open import Graded.Erasure.LogicalRelation as
open import Graded.Erasure.LogicalRelation.Assumptions.Reasoning
  is-reduction-relation
open import Graded.Erasure.LogicalRelation.Hidden UR as
open import Graded.Erasure.LogicalRelation.Value UR as
import Graded.Erasure.Target as T
import Graded.Erasure.Target.Properties as TP
open import Graded.Erasure.Target.Reasoning

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality

private variable
  n             : Nat
  Γ             : Con _ _
  γ δ η         : Conₘ _
  A B C t u v w : Term _
  l             : Lvl _
  m             : Mode

opaque

  -- Validity of Quot.

  Quotʳ :
    ts » Γ ⊢ l ∷Level →
    γ ▸ Γ ⊩ʳ Quot A B ∷[ m ∣ n ] U l
  Quotʳ ⊢l =
    ▸⊩ʳ∷⇔ .proj₂ λ ⊢σ _ →
    ®∷→®∷◂ $
    ®∷U⇔ .proj₂
      ( subst-⊢ ⊢l ⊢σ
      , U/Levelᵣ (λ { PE.refl → T.refl })
      )

opaque

  -- Validity of class.

  classʳ :
    ts » Γ ⊢ Quot A B →
    ts » Γ ⊢ t ∷ A →
    γ ▸ Γ ⊩ʳ t ∷[ m ∣ n ] A →
    γ ▸ Γ ⊩ʳ class t ∷[ m ∣ n ] Quot A B
  classʳ {m = 𝟘ᵐ} _ _ _ =
    ▸⊩ʳ∷[𝟘ᵐ]
  classʳ {m = 𝟙ᵐ} ⊢Q ⊢t ⊩ʳt =
    ▸⊩ʳ∷⇔ .proj₂ λ ⊢σ σ®σ′ →
    let ⊢t[σ] = subst-⊢ ⊢t ⊢σ in
    ®∷→®∷◂ $
    ®∷Quot⇔ .proj₂
      ( _
      , ⇒*→⇛ (id (class (subst-⊢ ⊢Q ⊢σ) ⊢t[σ]))
      , ®∷→®∷◂ω non-trivial (▸⊩ʳ∷⇔ .proj₁ ⊩ʳt ⊢σ σ®σ′)
      )

opaque

  -- Validity of resp.

  respʳ :
    Higher-quotient-constructors-allowed →
    m PE.≡ 𝟘ᵐ? →
    γ ▸ Γ ⊩ʳ resp A B t u v ∷[ m ∣ n ] C
  respʳ ok PE.refl =
    ▸⊩ʳ∷[𝟘ᵐ?] ok

opaque

  -- Validity of set.

  setʳ :
    Higher-quotient-constructors-allowed →
    m PE.≡ 𝟘ᵐ? →
    γ ▸ Γ ⊩ʳ set A B t u v w ∷[ m ∣ n ] C
  setʳ ok PE.refl =
    ▸⊩ʳ∷[𝟘ᵐ?] ok

opaque
  unfolding Is-set-Con Quot-rel-Con Resp-Con

  -- Validity of qrec.

  qrecʳ :
    ts » Γ ∙ Quot A B ⊢ C →
    ts » Γ ∙ A ⊢ t ∷ C [ class (var x0) ]↑ →
    δ ∙ ⌜ m ⌝ · ω ▸ Γ ∙ A ⊩ʳ t ∷[ m ∣ n ] C [ class (var x0) ]↑ →
    ts » Resp-Con Γ A B ⊢ u ∷ Resp-type A B C t →
    ts » Is-set-Con Γ A B C ⊢ v ∷ Is-set-type C →
    η ▸ Γ ⊩ʳ w ∷[ m ∣ n ] Quot A B →
    γ ≤ᶜ δ →
    γ ≤ᶜ η →
    γ ▸ Γ ⊩ʳ qrec C t u v w ∷[ m ∣ n ] C [ w ]₀
  qrecʳ {m = 𝟘ᵐ} _ _ _ _ _ _ _ _ =
    ▸⊩ʳ∷[𝟘ᵐ]
  qrecʳ
    {Γ} {A} {B} {C} {t} {m = 𝟙ᵐ} {u} {v} {w}
    ⊢C ⊢t ⊩ʳt ⊢u ⊢v ⊩ʳw γ≤δ γ≤η =
    ▸⊩ʳ∷⇔ .proj₂ λ {σ = σ} {σ′ = σ′} ⊢σ σ®σ′ →
    let w′ , w[σ]⇛class-w′ , w′® =
          ®∷Quot⇔ .proj₁ $
          ®∷→®∷◂ω non-trivial $
          ▸⊩ʳ∷⇔ .proj₁ ⊩ʳw ⊢σ
            (subsumption-®∷[∣]◂ (λ _ → ≤ᶜ→⟨⟩≡𝟘→⟨⟩≡𝟘 γ≤η) σ®σ′)

        _ , ⊢class-w′ =
          wf-⇛ w[σ]⇛class-w′

        ⊢w′ =
          inversion-class-Quot ⊢class-w′

        lemma :
          ∃ λ w″ →
          vs T.⊢ erase str w T.[ σ′ ] ⇒* w″ ×
          vs T.⊢ T.lam (erase str t) T.∘⟨ str ⟩ erase str w T.[ σ′ ] ⇒*
            erase str t T.[ T.consSubst σ′ w″ ]
        lemma =
          case PE.singleton str of λ where
            (T.non-strict , PE.refl) →
              erase str w T.[ σ′ ] ,
              T.refl ,
              (T.lam (erase str t T.[ σ′ T.⇑ ]) T.∘⟨ str ⟩
                 (erase str w T.[ σ′ ])                                 ⇒⟨ T.β-red _ ⟩

               erase str t T.[ σ′ T.⇑ ] T.[ erase str w T.[ σ′ ] ]₀     ≡⟨ TP.singleSubstComp _ _ (erase _ t) ⟩⇒

               erase str t T.[ T.consSubst σ′ (erase str w T.[ σ′ ]) ]  ∎⇒)
            (T.strict , PE.refl) →
              let w″ , w″-value , erase-w[σ′]⇒*w″ =
                    reduces-to-value PE.refl w′®
              in
              w″ ,
              erase-w[σ′]⇒*w″ ,
              (T.lam (erase str t T.[ σ′ T.⇑ ]) T.∘⟨ str ⟩
                 (erase str w T.[ σ′ ])                        ⇒*⟨ TP.app-subst*-arg T.lam erase-w[σ′]⇒*w″ ⟩

               T.lam (erase str t T.[ σ′ T.⇑ ]) T.∘⟨ str ⟩ w″  ⇒⟨ T.β-red w″-value ⟩

               erase str t T.[ σ′ T.⇑ ] T.[ w″ ]₀              ≡⟨ TP.singleSubstComp _ _ (erase _ t) ⟩⇒

               erase str t T.[ T.consSubst σ′ w″ ]             ∎⇒)

        w″ , erase-w[σ′]⇒w″ , lam∘[]⇒* =
          lemma

        w′®w″ =
          ®∷-⇒* erase-w[σ′]⇒w″ w′®

        t[σ,w″]® =
          ▸⊩ʳ∷⇔ .proj₁ ⊩ʳt {σ = consSubst _ _} {σ′ = T.consSubst _ _}
            (→⊢ˢʷ∷∙ ⊢σ ⊢w′) $
            ®∷[∣]∙◂∙⇔ .proj₂
              ( ®∷→®∷◂ w′®w″
              , subsumption-®∷[∣]◂ (λ _ → ≤ᶜ→⟨⟩≡𝟘→⟨⟩≡𝟘 γ≤δ) σ®σ′
              )

        ⊢C[σ⇑]  = subst-⊢-⇑ ⊢C ⊢σ
        ⊢t[σ⇑]  = PE.subst (_⊢_∷_ _ _) ([][]↑-commutes C) $
                  subst-⊢-⇑ ⊢t ⊢σ
        ⊢u[σ⇑³] = PE.subst₃ _⊢_∷_
                    (Resp-Con-[] Γ A B) PE.refl Resp-type-[] $
                  subst-⊢-⇑ ⊢u ⊢σ
        ⊢v[σ⇑⁵] = PE.subst₃ _⊢_∷_
                    (Is-set-Con-[] Γ A B C) PE.refl Is-set-type-[] $
                  subst-⊢-⇑ ⊢v ⊢σ

        w[σ]≡class-w′ =
          ⇛→⊢≡ w[σ]⇛class-w′

        C[σ⇑][w[σ]]≡ =
          C [ σ ⇑ ] [ w [ σ ] ]₀   ≡⟨ subst-⊢≡₀ ⊢C[σ⇑] w[σ]≡class-w′ ⟩⊢∎
          C [ σ ⇑ ] [ class w′ ]₀  ∎

        ≡C[σ⇑][w[σ]] =
          C [ class (var x0) ]↑ [ consSubst σ w′ ]  ≡˘⟨ singleSubstComp _ _ (C [ _ ]↑) ⟩⊢≡
          C [ class (var x0) ]↑ [ σ ⇑ ] [ w′ ]₀     ≡⟨ PE.cong _[ _ ]₀ ([][]↑-commutes C) ⟩⊢≡
          C [ σ ⇑ ] [ class (var x0) ]↑ [ w′ ]₀     ≡⟨ []↑-[]₀ (C [ _ ]) ⟩⊢≡
          C [ σ ⇑ ] [ class w′ ]₀                   ≡˘⟨ subst-⊢≡₀ ⊢C[σ⇑] w[σ]≡class-w′ ⟩⊢∎
          C [ σ ⇑ ] [ w [ σ ] ]₀                    ∎
    in
    conv-®∷◂
      (C [ class (var x0) ]↑ [ consSubst σ w′ ]  ≡⟨ ≡C[σ⇑][w[σ]] ⟩⊢∎≡
       C [ σ ⇑ ] [ w [ σ ] ]₀                    ≡˘⟨ singleSubstLift C _ ⟩
       C [ w ]₀ [ σ ]                            ∎) $
    ®∷◂-⇐*
      (             ∷ C [ class (var x0) ]↑ [ consSubst σ w′ ]          ⟨ ≡C[σ⇑][w[σ]] ⟩⇛

       qrec (C [ σ ⇑ ]) (t [ σ ⇑ ]) (u [ σ ⇑[ 3 ] ]) (v [ σ ⇑[ 5 ] ])
         (w [ σ ])  ∷ C [ σ ⇑ ] [ w [ σ ] ]₀                           ⇛⟨ qrec-⇛ ⊢C[σ⇑] ⊢t[σ⇑] ⊢u[σ⇑³] ⊢v[σ⇑⁵] w[σ]⇛class-w′ ⟩∷
                                                                        ⟨ C[σ⇑][w[σ]]≡ ⟩⇛
       qrec (C [ σ ⇑ ]) (t [ σ ⇑ ]) (u [ σ ⇑[ 3 ] ]) (v [ σ ⇑[ 5 ] ])
         (class w′) ∷ C [ σ ⇑ ] [ class w′ ]₀                          ⇛⟨ ⇒*→⇛ (redMany (qrec-β ⊢C[σ⇑] ⊢t[σ⇑] ⊢u[σ⇑³] ⊢v[σ⇑⁵] ⊢w′)) ⟩∎∷≡

       t [ σ ⇑ ] [ w′ ]₀                                               ≡⟨ singleSubstComp _ _ t ⟩

       t [ consSubst σ w′ ]                                            ∎)
      lam∘[]⇒* t[σ,w″]®
