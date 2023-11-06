------------------------------------------------------------------------
-- Some discussion of under what circumstances a []-cong combinator
-- can be defined
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
import Graded.Modality
open import Graded.Usage.Restrictions

module Graded.Box-cong
  {a} {M : Set a}
  (open Graded.Modality M)
  {𝕄 : Modality}
  (TR : Type-restrictions 𝕄)
  (UR : Usage-restrictions M)
  where

open Modality 𝕄
open Type-restrictions TR
open Usage-restrictions UR

open import Definition.Conversion.Consequences.Var TR
open import Definition.Typed TR
open import Definition.Typed.Consequences.Consistency TR
open import Definition.Typed.Consequences.DerivedRules TR
open import Definition.Typed.Consequences.Inversion TR
open import Definition.Typed.Consequences.Reduction TR
open import Definition.Typed.Properties TR
open import Definition.Typed.Reasoning.Reduction TR
import Definition.Typed.Weakening TR as W
open import Definition.Untyped M hiding (_∷_)
open import Definition.Untyped.Properties M

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Derived.Erased.Typed TR hiding ([]-cong′)
import Graded.Derived.Erased.Untyped 𝕄 as Erased
import Graded.Derived.Erased.Usage 𝕄 UR as ErasedU
open import Graded.Modality.Properties 𝕄
open import Graded.Mode 𝕄
open import Graded.Neutral TR UR
open import Graded.Reduction TR UR
open import Graded.Restrictions 𝕄
open import Graded.Usage 𝕄 UR
open import Graded.Usage.Inversion 𝕄 UR
open import Graded.Usage.Properties 𝕄 UR

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PartialOrder
open import Tools.Relation

private variable
  Γ             : Con Term _
  A B u         : Term _
  p q₁ q₂ q₃ q₄ : M
  s             : Strength

------------------------------------------------------------------------
-- Some lemmas

private opaque

  -- Some lemmas used below.

  ⊢₄ : ⊢ ε ∙ U ∙ var x0 ∙ var x1 ∙ Id (var x2) (var x1) (var x0)
  ⊢₄ = ⊢₃ ∙ Idⱼ (var ⊢₃ (there here)) (var ⊢₃ here)
    where
    ⊢₁ : ⊢ ε ∙ U
    ⊢₁ = ε ∙ Uⱼ ε

    ⊢₂ : ⊢ ε ∙ U ∙ var x0
    ⊢₂ = ⊢₁ ∙ univ (var ⊢₁ here)

    ⊢₃ : ⊢ ε ∙ U ∙ var x0 ∙ var x1
    ⊢₃ = ⊢₂ ∙ univ (var ⊢₂ (there here))

  ⊢₆ :
    ⊢ ε ∙ U ∙ var x0 ∙ var x1 ∙ Id (var x2) (var x1) (var x0) ∙ var x3 ∙
      Id (var x4) (var x3) (var x0)
  ⊢₆ =
    ⊢₅ ∙ Idⱼ (var ⊢₅ (there (there (there here)))) (var ⊢₅ here)
    where
    ⊢₅ :
      ⊢ ε ∙ U ∙ var x0 ∙ var x1 ∙ Id (var x2) (var x1) (var x0) ∙ var x3
    ⊢₅ = ⊢₄ ∙ univ (var ⊢₄ (there (there (there here))))

------------------------------------------------------------------------
-- Has-[]-cong

-- The property of supporting a []-cong combinator (with certain
-- grades).
--
-- Note that, unlike the []-cong primitive, the first argument must be
-- a type in U.

Has-[]-cong : Strength → M → M → M → M → Set a
Has-[]-cong s q₁ q₂ q₃ q₄ =
  let open Erased s in
  ∃ λ ([]-cong : Term 0) →
  ε ▸[ 𝟙ᵐ ] []-cong ×
  ε ⊢ []-cong ∷
    Π 𝟘 , q₁ ▷ U ▹
    Π 𝟘 , q₂ ▷ var x0 ▹
    Π 𝟘 , q₃ ▷ var x1 ▹
    Π 𝟘 , q₄ ▷ Id (var x2) (var x1) (var x0) ▹
    Id (Erased (var x3)) ([ var x2 ]) ([ var x1 ])

-- The property of supporting a []-cong combinator that computes
-- correctly.

Has-computing-[]-cong : Strength → M → M → M → M → Set a
Has-computing-[]-cong s q₁ q₂ q₃ q₄ =
  let open Erased s in
  ∃ λ (([]-cong′ , _) : Has-[]-cong s q₁ q₂ q₃ q₄) →
  ∀ n (Γ : Con Term n) (A t : Term n) →
  Γ ⊢ A ∷ U →
  Γ ⊢ t ∷ A →
  Γ ⊢ wk wk₀ []-cong′ ∘⟨ 𝟘 ⟩ A ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ rfl ⇒* rfl ∷
    Id (Erased A) ([ t ]) ([ t ])

opaque

  -- If the []-cong primitive is allowed, then []-cong is supported
  -- for grades for which "Π 𝟘" are allowed.

  []-cong→[]-cong :
    []-cong-allowed s →
    Π-allowed 𝟘 q₁ →
    Π-allowed 𝟘 q₂ →
    Π-allowed 𝟘 q₃ →
    Π-allowed 𝟘 q₄ →
    Has-computing-[]-cong s q₁ q₂ q₃ q₄
  []-cong→[]-cong {s} ok ok₁ ok₂ ok₃ ok₄ =
    case lamⱼ′ ok₁ $ lamⱼ′ ok₂ $ lamⱼ′ ok₃ $ lamⱼ′ ok₄ $
         []-congⱼ′ ok (var ⊢₄ here) of λ {
      ⊢[]-cong →
      ( []-cong′
      , (lamₘ $ lamₘ $ lamₘ $ lamₘ $
         sub ([]-congₘ var var var var) $ begin
           ε ∙ 𝟙 · 𝟘 ∙ 𝟙 · 𝟘 ∙ 𝟙 · 𝟘 ∙ 𝟙 · 𝟘  ≈⟨ ε ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ⟩
           𝟘ᶜ                                 ∎)
      , ⊢[]-cong
      )
    , λ _ _ A t ⊢A ⊢t →
        wk wk₀ []-cong′ ∘⟨ 𝟘 ⟩ A ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ rfl  ⇒*⟨ β-red-⇒₄ (W.wkTerm W.wk₀∷⊇ (wfTerm ⊢A) ⊢[]-cong) ⊢A ⊢t ⊢t (rflⱼ ⊢t) ⟩
        []-cong s A t t rfl                                    ⇒⟨ []-cong-β-⇒ (refl ⊢t) ok ⟩∎
        rfl                                                    ∎ }
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset

    []-cong′ : Term 0
    []-cong′ =
      lam 𝟘 $ lam 𝟘 $ lam 𝟘 $ lam 𝟘 $
      []-cong s (var x3) (var x2) (var x1) (var x0)

opaque

  -- If erased matches are allowed for J and the type Erased is
  -- allowed, then []-cong is supported for grades for which "Π 𝟘" are
  -- allowed.

  J₀→[]-cong :
    Erased-matches-for-J →
    Erased-allowed s →
    Π-allowed 𝟘 q₁ →
    Π-allowed 𝟘 q₂ →
    Π-allowed 𝟘 q₃ →
    Π-allowed 𝟘 q₄ →
    Has-computing-[]-cong s q₁ q₂ q₃ q₄
  J₀→[]-cong {s} J₀-ok Erased-ok ok₁ ok₂ ok₃ ok₄ =
    case lamⱼ′ ok₁ $ lamⱼ′ ok₂ $ lamⱼ′ ok₃ $ lamⱼ′ ok₄ $
         Jⱼ′
           (Idⱼ
              ([]ⱼ Erased-ok
                 (var ⊢₆ (there (there (there (there here))))))
              ([]ⱼ Erased-ok (var ⊢₆ (there here))))
           (rflⱼ ([]ⱼ Erased-ok (var ⊢₄ (there (there here)))))
           (var ⊢₄ here) of λ {
      ⊢[]-cong →
      ( []-cong′
      , (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
         lamₘ $ lamₘ $ lamₘ $ lamₘ $
         sub (J₀ₘ J₀-ok var var ▸Id rflₘ var var) $ begin
           ε ∙ 𝟙 · 𝟘 ∙ 𝟙 · 𝟘 ∙ 𝟙 · 𝟘 ∙ 𝟙 · 𝟘  ≈⟨ ε ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ⟩
           𝟘ᶜ                                 ∎)
      , ⊢[]-cong
      )
    , λ _ _ A t ⊢A ⊢t →
        case wfTerm ⊢A ∙ univ ⊢A of λ {
          ⊢Γ∙A →
        case Idⱼ (W.wkTerm₁ (univ ⊢A) ⊢t) (var ⊢Γ∙A here) of λ {
          ⊢Id →
        case PE.cong₂
               (λ A′ t′ → Id (Erased A′) ([ t′ ]) ([ t ]))
               (PE.trans (wk2-tail A) (subst-id A))
               (PE.trans (wk2-tail t) (subst-id t)) of λ {
          lemma →
        wk wk₀ []-cong′ ∘⟨ 𝟘 ⟩ A ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ rfl  ⇒*⟨ β-red-⇒₄ (W.wkTerm W.wk₀∷⊇ (wfTerm ⊢A) ⊢[]-cong) ⊢A ⊢t ⊢t (rflⱼ ⊢t) ⟩

        J 𝟘 𝟘 A t
          (Id (Erased (wk1 (wk1 A))) ([ wk1 (wk1 t) ])
             ([ var x1 ]))
          rfl t rfl                                            ⇒⟨ PE.subst (_⊢_⇒_∷_ _ _ _) lemma $
                                                                  J-β-⇒ (refl ⊢t)
                                                                    (Idⱼ
                                                                       ([]ⱼ Erased-ok $
                                                                        W.wkTerm₁ ⊢Id (W.wkTerm₁ (univ ⊢A) ⊢t))
                                                                       ([]ⱼ Erased-ok (var (⊢Γ∙A ∙ ⊢Id) (there here))))
                                                                    (PE.subst (_⊢_∷_ _ _) (PE.sym lemma) $
                                                                     rflⱼ ([]ⱼ Erased-ok ⊢t)) ⟩∎
        rfl                                                    ∎ }}}}
    where
    open Erased s
    open ErasedU s

    []-cong′ : Term 0
    []-cong′ =
      lam 𝟘 $ lam 𝟘 $ lam 𝟘 $ lam 𝟘 $
      J 𝟘 𝟘 (var x3) (var x2)
        (Id (Erased (var x5)) ([ var x4 ]) ([ var x1 ]))
        rfl (var x1) (var x0)

    lemma : 𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘 ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘 ≈ᶜ 𝟘ᶜ {n = 6}
    lemma = ≈ᶜ-refl ∙ ·-zeroʳ _ ∙ ·-zeroʳ _

    ▸Id :
      𝟘ᶜ {n = 4} ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘 ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘 ▸[ 𝟘ᵐ? ]
        Id (Erased (var x5)) ([ var x4 ]) ([ var x1 ])
    ▸Id = Idₘ′ (▸Erased var) (▸[] var) (▸[] var)
      (begin
         𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘 ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ lemma ⟩
         𝟘ᶜ                              ∎)
      (begin
         𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘 ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ lemma ⟩
         𝟘ᶜ                              ≈˘⟨ +ᶜ-identityʳ _ ⟩
         𝟘ᶜ +ᶜ 𝟘ᶜ                        ∎)
      where
      open Tools.Reasoning.PartialOrder ≤ᶜ-poset

opaque

  -- If the modality's zero is well-behaved and erased matches
  -- (including the []-cong primitive) are not allowed, then []-cong
  -- is not supported (with any grades).

  ¬-[]-cong :
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero semiring-with-meet ⦄ →
    No-erased-matches TR UR →
    ¬ Has-[]-cong s q₁ q₂ q₃ q₄
  ¬-[]-cong nem (_ , ▸[]-cong , ⊢[]-cong) =
    case lemma
           (lemma
              (lemma
                 (lemma (idSubst , id , _ , ▸[]-cong , ⊢[]-cong) (ℕⱼ ε))
                 (zeroⱼ ε))
              (zeroⱼ ε))
           (rflⱼ (zeroⱼ ε)) of λ {
      (_ , ⊢σ , _ , ▸t , ⊢t) →
    case red-Id ⊢t of λ where
      (_ , rflₙ , ⇒*rfl) →
        case var-only-equal-to-itself (neₙ (var _)) (ne (var _)) $
             prod-cong⁻¹ (inversion-rfl-Id (⊢u-redₜ ⇒*rfl))
               .proj₂ .proj₁ of λ ()
      (_ , ne u-ne , t⇒*u) →
        neutral-not-well-resourced nem (inhabited-consistent ⊢σ) u-ne
          (⊢u-redₜ t⇒*u) (usagePres*Term ▸t (redₜ t⇒*u)) }
    where
    lemma :
      ((σ , _) :
       ∃ λ σ → ε ⊢ˢ σ ∷ Γ ×
       ∃ λ t → 𝟘ᶜ ▸[ 𝟙ᵐ ] t × Γ ⊢ t ∷ Π 𝟘 , p ▷ A ▹ B) →
      ε ⊢ u ∷ A [ σ ] →
      (∃ λ σ → ε ⊢ˢ σ ∷ Γ ∙ A ×
       ∃ λ t → 𝟘ᶜ ▸[ 𝟙ᵐ ] t × Γ ∙ A ⊢ t ∷ B)
    lemma (_ , ⊢σ , _ , ▸t , ⊢t) ⊢u =
        consSubst _ _
      , (⊢σ , ⊢u)
      , (case red-Π ⊢t of λ where
           (_ , ne v-n , t⇒*v) →
             ⊥-elim $
             neutral-not-well-resourced nem (inhabited-consistent ⊢σ)
               v-n (⊢u-redₜ t⇒*v) (usagePres*Term ▸t (redₜ t⇒*v))
           (lam _ v , lamₙ , t⇒*lam) →
             case inv-usage-lam (usagePres*Term ▸t (redₜ t⇒*lam)) of λ {
               (invUsageLam ▸v 𝟘≤) →
             case inversion-lam-Π (⊢u-redₜ t⇒*lam) of λ {
               (⊢v , PE.refl , _) →
               _
             , sub ▸v (𝟘≤ ∙ ≤-reflexive (PE.sym (·-zeroʳ _)))
             , ⊢v }})
