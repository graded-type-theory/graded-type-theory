------------------------------------------------------------------------
-- Some instances of Has-[]-cong/Has-computing-[]-cong are logically
-- equivalent
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
import Graded.Modality
import Graded.Mode.Instances.Zero-one
open import Graded.Mode.Instances.Zero-one.Variant
open import Graded.Usage.Restrictions

module Graded.Has-box-cong.Equivalent
  {a} {M : Set a}
  (open Graded.Modality M)
  {𝕄 : Modality}
  {variant : Mode-variant 𝕄}
  (open Graded.Mode.Instances.Zero-one variant)
  (TR : Type-restrictions 𝕄)
  (UR : Usage-restrictions 𝕄 Zero-one-isMode)
  where

open Modality 𝕄
open Mode-variant variant
open Type-restrictions TR
open Usage-restrictions UR

open import Definition.Typed TR
open import Definition.Typed.Inversion TR
open import Definition.Typed.Properties TR as P hiding ([]-cong′)
open import Definition.Typed.Reasoning.Term TR
open import Definition.Typed.Weakening TR as W using (_»_∷ʷ_⊇_)
import Definition.Typed.Weakening.Definition TR as WD
open import Definition.Typed.Well-formed TR
open import Definition.Untyped M as U
import Definition.Untyped.Erased 𝕄 as Erased
open import Definition.Untyped.Identity 𝕄
open import Definition.Untyped.Properties M

open import Graded.Has-box-cong TR UR
open import Graded.Has-box-cong.Lemmas TR variant
open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
import Graded.Derived.Erased.Usage UR as ErasedU
import Graded.Derived.Erased.Usage.Zero-one UR as ErasedU₀₁
open import Graded.Derived.Identity UR
open import Graded.Modality.Properties 𝕄
open import Graded.Usage UR
open import Graded.Usage.Weakening UR

open import Tools.Bool using (T)
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 5+)
open import Tools.Product
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation

private variable
  n n′                                 : Nat
  Δ                                    : Con Term _
  t u v w                              : Term _
  p₁ p₁′ p₂ p₂′ p₃ p₃′ p₄ p₄′
    q₁ q₁′ q₂ q₂′ q₃ q₃′ q₄ q₄′ q₅ q₅′ : M
  m                                    : Mode
  s                                    : Strength

------------------------------------------------------------------------
-- Some instances of Has-[]-cong/Has-computing-[]-cong are logically
-- equivalent

-- Some definitions/lemmas used below.

private
  module Has-[]-cong-weaker
    {Γ : Con Term n}
    (hyp₁ : Π-allowed p₁ q₁ → Π-allowed p₁′ q₁′)
    (hyp₂ : Π-allowed p₂ q₂ → Π-allowed p₂′ q₂′)
    (hyp₃ : Π-allowed p₃ q₃ → Π-allowed p₃′ q₃′)
    (hyp₄ : Π-allowed p₄ q₄ → Π-allowed p₄′ q₄′)
    (hyp₅ : Π-allowed 𝟘  q₅ → Π-allowed 𝟘   q₅′)
    (has-[]-cong@([]-cong′ , _ , ⊢[]-cong′) :
     Has-[]-cong s m Γ p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ q₅)
    where

    open Erased s

    []-cong″ : Term (5+ n)
    []-cong″ =
       wk (stepn id 5) []-cong′ ∘⟨ p₁ ⟩ var x4 ∘⟨ p₂ ⟩ var x3
         ∘⟨ p₃ ⟩ var x2 ∘⟨ p₄ ⟩ var x1 ∘⟨ 𝟘 ⟩ var x0

    opaque
      unfolding Erased [_]

      ⊢[]-cong″ :
        ε » Γ ∙ Level ∙ U (level (var x0)) ∙ var x0 ∙ var x1 ∙
          Id (var x2) (var x1) (var x0) ⊢
          []-cong″ ∷
          Id (Erased (level (var x4)) (var x3)) [ var x2 ] ([ var x1 ])
      ⊢[]-cong″ =
        flip _∘ⱼ_ (var₀ ⊢Id) $
        flip _∘ⱼ_ (var₁ ⊢Id) $
        flip _∘ⱼ_ (var₂ ⊢Id) $
        flip _∘ⱼ_ (var₃ ⊢Id) $
        flip _∘ⱼ_ (var₄ ⊢Id) $
        WD.defn-wk (WD.»⊇ε ε) $
        W.wk (W.ʷ⊇-drop (∙ ⊢Id)) ⊢[]-cong′
        where
        ⊢Id :
          ε » Γ ∙ Level ∙ U (level (var x0)) ∙ var x0 ∙ var x1 ⊢
          Id (var x2) (var x1) (var x0)
        ⊢Id =
          ⊢Id-2-1-0 (Has-[]-cong→Level-allowed has-[]-cong)
            (wf ⊢[]-cong′)

    oks :
      Π-allowed p₁′ q₁′ × Π-allowed p₂′ q₂′ × Π-allowed p₃′ q₃′ ×
      Π-allowed p₄′ q₄′ × Π-allowed 𝟘 q₅′
    oks =
      let _ , ⊢Π , ok₁ = inversion-ΠΣ $ wf-⊢ ⊢[]-cong′
          _ , ⊢Π , ok₂ = inversion-ΠΣ ⊢Π
          _ , ⊢Π , ok₃ = inversion-ΠΣ ⊢Π
          _ , ⊢Π , ok₄ = inversion-ΠΣ ⊢Π
          _ , _  , ok₅ = inversion-ΠΣ ⊢Π
      in
      hyp₁ ok₁ , hyp₂ ok₂ , hyp₃ ok₃ , hyp₄ ok₄ , hyp₅ ok₅

opaque

  -- One can make the "p" grades of Has-[]-cong "smaller" (given
  -- certain assumptions).

  Has-[]-cong-weaker :
    {Γ : Con Term n} →
    (Π-allowed p₁ q₁ → Π-allowed p₁′ q₁′) →
    (Π-allowed p₂ q₂ → Π-allowed p₂′ q₂′) →
    (Π-allowed p₃ q₃ → Π-allowed p₃′ q₃′) →
    (Π-allowed p₄ q₄ → Π-allowed p₄′ q₄′) →
    (Π-allowed 𝟘  q₅ → Π-allowed 𝟘   q₅′) →
    ⌜ m ⌝ · p₁′ ≤ ⌜ m ⌝ · p₁ →
    ⌜ m ⌝ · p₂′ ≤ ⌜ m ⌝ · p₂ →
    ⌜ m ⌝ · p₃′ ≤ ⌜ m ⌝ · p₃ →
    ⌜ m ⌝ · p₄′ ≤ ⌜ m ⌝ · p₄ →
    Has-[]-cong s m Γ p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ q₅ →
    Has-[]-cong s m Γ p₁′ q₁′ p₂′ q₂′ p₃′ q₃′ p₄′ q₄′ q₅′
  Has-[]-cong-weaker
    {n} {p₁} {p₁′} {q₁′} {p₂} {p₂′} {q₂′} {p₃} {p₃′} {q₃′}
    {p₄} {p₄′} {q₄′} {q₅′} {m} {s} {Γ}
    hyp₁ hyp₂ hyp₃ hyp₄ hyp₅ hyp₁′ hyp₂′ hyp₃′ hyp₄′
    has-[]-cong@(_ , ▸[]-cong′ , _) =
    []-cong‴ , ▸[]-cong‴ , ⊢[]-cong‴
    where
    open Erased s
    open Has-[]-cong-weaker hyp₁ hyp₂ hyp₃ hyp₄ hyp₅ has-[]-cong

    []-cong‴ : Term n
    []-cong‴ = lam p₁′ $ lam p₂′ $ lam p₃′ $ lam p₄′ $ lam 𝟘 []-cong″

    ▸[]-cong‴ : 𝟘ᶜ ▸[ m ] []-cong‴
    ▸[]-cong‴ =
      lamₘ $ lamₘ $ lamₘ $ lamₘ $ lamₘ $
      sub
        (((((wkUsage (stepn id 5) ▸[]-cong′ ∘ₘ var) ∘ₘ var) ∘ₘ var) ∘ₘ
          var) ∘ₘ
         var) $
      (begin
         𝟘ᶜ ∙ ⌜ m ⌝ · p₁′ ∙ ⌜ m ⌝ · p₂′ ∙ ⌜ m ⌝ · p₃′ ∙ ⌜ m ⌝ · p₄′ ∙
         ⌜ m ⌝ · 𝟘                                                     ≤⟨ ≤ᶜ-refl ∙ hyp₁′ ∙ hyp₂′ ∙ hyp₃′ ∙ hyp₄′ ∙ ≤-reflexive (·-zeroʳ _) ⟩

         𝟘ᶜ ∙ ⌜ m ⌝ · p₁ ∙ ⌜ m ⌝ · p₂ ∙ ⌜ m ⌝ · p₃ ∙ ⌜ m ⌝ · p₄ ∙ 𝟘    ≈˘⟨ ≈ᶜ-trans (+ᶜ-congˡ (·ᶜ-zeroˡ _)) $
                                                                           ≈ᶜ-trans (+ᶜ-identityʳ _) $
                                                                           ≈ᶜ-trans
                                                                             (+ᶜ-cong
                                                                                (+ᶜ-cong
                                                                                   (+ᶜ-cong (≈ᶜ-trans (+ᶜ-identityˡ _) (·ᶜ𝟘ᶜ,≔⌜ᵐ·⌝ m x4))
                                                                                      (·ᶜ𝟘ᶜ,≔⌜ᵐ·⌝ m x3))
                                                                                   (·ᶜ𝟘ᶜ,≔⌜ᵐ·⌝ m x2))
                                                                                (·ᶜ𝟘ᶜ,≔⌜ᵐ·⌝ m x1))
                                                                             ((≈ᶜ-trans (+ᶜ-identityʳ _) $
                                                                               ≈ᶜ-trans (+ᶜ-identityʳ _) $
                                                                               +ᶜ-identityʳ _) ∙
                                                                              (PE.trans (+-identityʳ _) $
                                                                               PE.trans (+-identityʳ _) $
                                                                               +-identityˡ _) ∙
                                                                              (PE.trans (+-identityʳ _) $
                                                                               PE.trans (+-congʳ (+-identityʳ _)) $
                                                                               +-identityˡ _) ∙
                                                                              (PE.trans
                                                                                 (+-congʳ $
                                                                                  (PE.trans (+-identityʳ _) $
                                                                                   +-identityʳ _)) $
                                                                               +-identityˡ _ ) ∙
                                                                              (PE.trans (+-identityʳ _) $
                                                                               PE.trans (+-identityʳ _) $
                                                                               +-identityʳ _)) ⟩
         ((((𝟘ᶜ +ᶜ p₁ ·ᶜ (𝟘ᶜ , x4 ≔ ⌜ m ᵐ· p₁ ⌝)) +ᶜ
            p₂ ·ᶜ (𝟘ᶜ , x3 ≔ ⌜ m ᵐ· p₂ ⌝)) +ᶜ
           p₃ ·ᶜ (𝟘ᶜ , x2 ≔ ⌜ m ᵐ· p₃ ⌝)) +ᶜ
          p₄ ·ᶜ (𝟘ᶜ , x1 ≔ ⌜ m ᵐ· p₄ ⌝)) +ᶜ
         𝟘 ·ᶜ (𝟘ᶜ , x0 ≔ ⌜ m ᵐ· 𝟘 ⌝)                                   ∎)
      where
      open ≤ᶜ-reasoning

    ⊢[]-cong‴ :
      ε » Γ ⊢ []-cong‴ ∷
        Π p₁′ , q₁′ ▷ Level ▹
        Π p₂′ , q₂′ ▷ U (level (var x0)) ▹
        Π p₃′ , q₃′ ▷ var x0 ▹
        Π p₄′ , q₄′ ▷ var x1 ▹
        Π 𝟘   , q₅′ ▷ Id (var x2) (var x1) (var x0) ▹
        Id (Erased (level (var x4)) (var x3)) ([ var x2 ]) ([ var x1 ])
    ⊢[]-cong‴ =
      let ok₁ , ok₂ , ok₃ , ok₄ , ok₅ = oks in
      lamⱼ′ ok₁ $ lamⱼ′ ok₂ $ lamⱼ′ ok₃ $ lamⱼ′ ok₄ $
      lamⱼ′ ok₅ ⊢[]-cong″

opaque
  unfolding Has-[]-cong-weaker Erased.Erased Erased.[_]

  -- One can make the "p" grades of Has-computing-[]-cong "smaller"
  -- (given certain assumptions).

  Has-computing-[]-cong-weaker :
    (Π-allowed p₁ q₁ → Π-allowed p₁′ q₁′) →
    (Π-allowed p₂ q₂ → Π-allowed p₂′ q₂′) →
    (Π-allowed p₃ q₃ → Π-allowed p₃′ q₃′) →
    (Π-allowed p₄ q₄ → Π-allowed p₄′ q₄′) →
    (Π-allowed 𝟘  q₅ → Π-allowed 𝟘   q₅′) →
    ⌜ m ⌝ · p₁′ ≤ ⌜ m ⌝ · p₁ →
    ⌜ m ⌝ · p₂′ ≤ ⌜ m ⌝ · p₂ →
    ⌜ m ⌝ · p₃′ ≤ ⌜ m ⌝ · p₃ →
    ⌜ m ⌝ · p₄′ ≤ ⌜ m ⌝ · p₄ →
    Has-computing-[]-cong s m Δ p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ q₅ →
    Has-computing-[]-cong s m Δ p₁′ q₁′ p₂′ q₂′ p₃′ q₃′ p₄′ q₄′ q₅′
  Has-computing-[]-cong-weaker
    {p₁} {p₁′} {p₂} {p₂′} {p₃} {p₃′} {p₄} {p₄′}
    hyp₁ hyp₂ hyp₃ hyp₄ hyp₅ hyp₁′ hyp₂′ hyp₃′ hyp₄′
    (has-[]-cong@([]-cong′ , _ , ⊢[]-cong′) , []-cong′≡) =
    let open Has-[]-cong-weaker hyp₁ hyp₂ hyp₃ hyp₄ hyp₅ has-[]-cong

        ok = Has-[]-cong→Level-allowed has-[]-cong

        ok₁ , ok₂ , ok₃ , ok₄ , ok₅ = oks
    in
      Has-[]-cong-weaker hyp₁ hyp₂ hyp₃ hyp₄ hyp₅
        hyp₁′ hyp₂′ hyp₃′ hyp₄′ has-[]-cong
    , λ _ _ _ l A t ρ Δ⊇Γ ⊢A ⊢t →
        let ⊇ε = WD.»⊇ε (defn-wf (wf ⊢A)) in
        wk ρ
          (lam p₁′ $ lam p₂′ $ lam p₃′ $ lam p₄′ $ lam 𝟘 $
           wk (stepn id 5) []-cong′ ∘⟨ p₁ ⟩ var x4 ∘⟨ p₂ ⟩ var x3
             ∘⟨ p₃ ⟩ var x2 ∘⟨ p₄ ⟩ var x1 ∘⟨ 𝟘 ⟩ var x0)
          ∘⟨ p₁′ ⟩ l ∘⟨ p₂′ ⟩ A ∘⟨ p₃′ ⟩ t ∘⟨ p₄′ ⟩ t ∘⟨ 𝟘 ⟩ rfl          ⇒*⟨ β-red-⇒₅′ ok₁ ok₂ ok₃ ok₄ ok₅
                                                                                (W.wk
                                                                                  (W.liftnʷ Δ⊇Γ $ ∙_ $ ⊢Id-2-1-0 ok $ wf $
                                                                                   WD.defn-wk ⊇ε ⊢[]-cong′) $
                                                                                  WD.defn-wk ⊇ε ⊢[]-cong″)
                                                                                (⊢∷Level→⊢∷Level ok (inversion-U-Level (wf-⊢ ⊢A)))
                                                                                ⊢A ⊢t ⊢t (rflⱼ ⊢t) ⟩⊢
        (wk (liftn ρ 5) (wk (stepn id 5) []-cong′)
           [ consSubst
               (consSubst (consSubst (consSubst (sgSubst l) A) t) t)
               rfl ])
          ∘⟨ p₁ ⟩ l ∘⟨ p₂ ⟩ A ∘⟨ p₃ ⟩ t ∘⟨ p₄ ⟩ t ∘⟨ 𝟘 ⟩ rfl              ≡⟨ PE.cong
                                                                               (λ []-cong → []-cong ∘⟨ _ ⟩ _ ∘⟨ _ ⟩ _ ∘⟨ _ ⟩ _ ∘⟨ _ ⟩ _ ∘⟨ _ ⟩ _) $
                                                                             PE.trans
                                                                               (PE.cong _[ _ ] $
                                                                                PE.trans (wk-comp _ _ []-cong′) $
                                                                                PE.cong (flip wk _) $
                                                                                PE.sym $ liftn-stepn-comp 5) $
                                                                             PE.trans (subst-wk []-cong′) $
                                                                             PE.sym $ wk≡subst _ _ ⟩⊢≡

        wk ρ []-cong′ ∘⟨ p₁ ⟩ l ∘⟨ p₂ ⟩ A ∘⟨ p₃ ⟩ t ∘⟨ p₄ ⟩ t ∘⟨ 𝟘 ⟩ rfl  ≡⟨ []-cong′≡ _ _ _ _ _ _ _ Δ⊇Γ ⊢A ⊢t ⟩⊢∎

        rfl                                                               ∎

-- Some definitions/lemmas used below.

private
  module Has-[]-cong-stronger
    {Γ : Con Term n}
    (hyp₁ : Π-allowed p₁ q₁ → Π-allowed p₁′ q₁′)
    (hyp₂ : Π-allowed p₂ q₂ → Π-allowed p₂′ q₂′)
    (hyp₃ : Π-allowed p₃ q₃ → Π-allowed p₃′ q₃′)
    (hyp₄ : Π-allowed p₄ q₄ → Π-allowed p₄′ q₄′)
    (hyp₅ : Π-allowed 𝟘  q₅ → Π-allowed 𝟘   q₅′)
    (has-[]-cong@([]-cong′ , _ , ⊢[]-cong′) :
     Has-[]-cong s m Γ p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ q₅)
    where

    open Erased s

    []-cong″ : Term (5+ n)
    []-cong″ =
      cong 𝟘
        (Erased (level (var x4)) (Erased (level (var x4)) (var x3)))
        [ [ var x2 ] ] [ [ var x1 ] ] (Erased (level (var x4)) (var x3))
        (mapᴱ (Erased (level (var x5)) (var x4))
           (erased (var x5) (var x0)) (var x0))
        (wk (stepn id 5) []-cong′ ∘⟨ p₁ ⟩ var x4
           ∘⟨ p₂ ⟩ Erased (level (var x4)) (var x3) ∘⟨ p₃ ⟩ [ var x2 ]
           ∘⟨ p₄ ⟩ [ var x1 ]
           ∘⟨ 𝟘 ⟩ cong 𝟘 (var x3) (var x2) (var x1)
                    (Erased (level (var x4)) (var x3)) [ var x0 ]
                    (var x0))

    opaque
      unfolding Erased [_]

      ⊢[]-cong″ :
        Π-allowed p₁′ q₁′ × Π-allowed p₂′ q₂′ ×
        Π-allowed p₃′ q₃′ × Π-allowed p₄′ q₄′ ×
        Π-allowed 𝟘 q₅′ ×
        ε »
        Γ ∙ Level ∙ U (level (var x0)) ∙ var x0 ∙ var x1 ∙
          Id (var x2) (var x1) (var x0) ⊢
        []-cong″ ∷
        Id (Erased (level (var x4)) (var x3)) [ var x2 ] ([ var x1 ])
      ⊢[]-cong″ =
        let ok               = Has-[]-cong→Level-allowed has-[]-cong
            _ , ⊢Π  , ok₁    = inversion-ΠΣ $ wf-⊢ ⊢[]-cong′
            _ , ⊢Π  , ok₂    = inversion-ΠΣ ⊢Π
            _ , ⊢Π  , ok₃    = inversion-ΠΣ ⊢Π
            _ , ⊢Π  , ok₄    = inversion-ΠΣ ⊢Π
            _ , ⊢Id , ok₅    = inversion-ΠΣ ⊢Π
            Erased-ok , _    = inversion-Erased $
                               inversion-Id ⊢Id .proj₁
            ⊢Id              = ⊢Id-2-1-0 ok (wf ⊢[]-cong′)
            ⊢3               = var₃ ⊢Id
            ⊢4               = term ok (var₄ ⊢Id)
            ⊢Erased-3        = Erasedⱼ-U Erased-ok ⊢3
            ⊢Erased-Erased-3 = univ (Erasedⱼ-U Erased-ok ⊢Erased-3)
            ⊢5               = term ok (var₅ ⊢Erased-Erased-3)

            lemma :
              ∀ t →
              ε »
                Γ ∙ Level ∙ U (level (var x0)) ∙ var x0 ∙ var x1 ∙
                  Id (var x2) (var x1) (var x0) ⊢
                t ∷ var x3 →
              ε »
                Γ ∙ Level ∙ U (level (var x0)) ∙ var x0 ∙ var x1 ∙
                  Id (var x2) (var x1) (var x0) ⊢
                mapᴱ (Erased (level (var x5)) (var x4))
                  (erased (var x5) (var x0)) (var x0) [ [ [ t ] ] ]₀ ≡
                [ t ] ∷ Erased (level (var x4)) (var x3)
            lemma t ⊢t =
              mapᴱ (Erased (level (var x5)) (var x4))
                (erased (var x5) (var x0)) (var x0) [ [ [ t ] ] ]₀  ≡⟨ PE.trans mapᴱ-[] $
                                                                       PE.cong₂ (mapᴱ _) erased-[] PE.refl ⟩⊢≡
              mapᴱ (Erased (level (var x4)) (var x3))
                (erased (var x4) (var x0)) ([ [ t ] ])              ≡⟨ mapᴱ-β Erased-ok ⊢4 (erasedⱼ (var₀ (univ ⊢Erased-3)))
                                                                         ([]ⱼ Erased-ok ⊢4 ⊢t) ⟩⊢

              [ erased (var x4) (var x0) [ [ t ] ]₀ ]               ≡⟨ PE.cong [_] erased-[] ⟩⊢≡

              [ erased (var x3) ([ t ]) ]                           ≡⟨ P.[]-cong′ Erased-ok ⊢4 $
                                                                       Erased-β Erased-ok ⊢t ⟩⊢∎
              [ t ]                                                 ∎
        in
        hyp₁ ok₁ , hyp₂ ok₂ , hyp₃ ok₃ , hyp₄ ok₄ , hyp₅ ok₅ ,
        _⊢_∷_.conv
          (⊢cong
             (⊢mapᴱ ⊢5
                (erasedⱼ $ var₀ $ Erasedⱼ Erased-ok ⊢5 $
                 univ (var₄ ⊢Erased-Erased-3))
                (var₀ ⊢Erased-Erased-3)) $
           flip _∘ⱼ_
             (⊢cong
                ([]ⱼ Erased-ok (term ok (var₅ (univ ⊢3))) $
                 var₀ (univ ⊢3)) $
              var₀ ⊢Id) $
           flip _∘ⱼ_ ([]ⱼ Erased-ok ⊢4 $ var₁ ⊢Id) $
           flip _∘ⱼ_ ([]ⱼ Erased-ok ⊢4 $ var₂ ⊢Id) $
           flip _∘ⱼ_ (Erasedⱼ-U Erased-ok $ var₃ ⊢Id) $
           flip _∘ⱼ_ (var₄ ⊢Id) $
            W.wk (W.ʷ⊇-drop (∙ ⊢Id)) ⊢[]-cong′)
          (Id-cong (refl (univ ⊢Erased-3)) (lemma _ (var₂ ⊢Id))
             (lemma _ (var₁ ⊢Id)))

opaque

  -- One can replace some of the "p" grades in Has-[]-cong with grades
  -- that satisfy certain assumptions (given certain assumptions).
  --
  -- Note that, if all Π-types are allowed, then all but one of the
  -- assumptions (⌜ m ⌝ · p₁′ ≤ ⌜ m ⌝ · ω · p₁) are satisfied for the
  -- erasure modality with 𝟘ᵐ.

  Has-[]-cong-stronger :
    {Γ : Con Term n} →
    (s PE.≡ 𝕨 → ¬ T 𝟘ᵐ-allowed → Trivial) →
    (s PE.≡ 𝕨 → Prodrec-allowed 𝟘ᵐ? (𝟘 ∧ 𝟙) 𝟘 𝟘) →
    (s PE.≡ 𝕤 → ¬ T 𝟘ᵐ-allowed → 𝟘 ≤ 𝟙) →
    (Π-allowed p₁ q₁ → Π-allowed p₁′ q₁′) →
    (Π-allowed p₂ q₂ → Π-allowed p₂′ q₂′) →
    (Π-allowed p₃ q₃ → Π-allowed p₃′ q₃′) →
    (Π-allowed p₄ q₄ → Π-allowed p₄′ q₄′) →
    (Π-allowed 𝟘  q₅ → Π-allowed 𝟘   q₅′) →
    ⌜ m ⌝ · p₁′ ≤ ⌜ m ⌝ · ω · p₁ →
    ⌜ m ⌝ · p₂′ ≤ 𝟘 →
    ⌜ m ⌝ · p₃′ ≤ 𝟘 →
    ⌜ m ⌝ · p₄′ ≤ 𝟘 →
    Has-[]-cong s m Γ p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ q₅ →
    Has-[]-cong s m Γ p₁′ q₁′ p₂′ q₂′ p₃′ q₃′ p₄′ q₄′ q₅′
  Has-[]-cong-stronger
    {n} {s} {p₁} {p₁′} {q₁′} {p₂} {p₂′} {q₂′} {p₃} {p₃′} {q₃′}
    {p₄} {p₄′} {q₄′} {q₅′} {m} {Γ}
    trivial P-ok 𝟘≤𝟙 hyp₁ hyp₂ hyp₃ hyp₄ hyp₅ hyp₁′ hyp₂′ hyp₃′ hyp₄′
    has-[]-cong@(_ , ▸[]-cong′ , _) =
    []-cong‴ , ▸[]-cong‴ , ⊢[]-cong‴
    where
    open Erased s
    open ErasedU s using (▸Erased; ▸[])
    open ErasedU₀₁ s
    open Has-[]-cong-stronger hyp₁ hyp₂ hyp₃ hyp₄ hyp₅ has-[]-cong

    []-cong‴ : Term n
    []-cong‴ =
      lam p₁′ $ lam p₂′ $ lam p₃′ $ lam p₄′ $ lam 𝟘 []-cong″

    opaque

      ⊢[]-cong‴ :
        ε » Γ ⊢ []-cong‴ ∷
        Π p₁′ , q₁′ ▷ Level ▹
        Π p₂′ , q₂′ ▷ U (level (var x0)) ▹
        Π p₃′ , q₃′ ▷ var x0 ▹
        Π p₄′ , q₄′ ▷ var x1 ▹
        Π 𝟘   , q₅′ ▷ Id (var x2) (var x1) (var x0) ▹
        Id (Erased (level (var x4)) (var x3)) [ var x2 ] ([ var x1 ])
      ⊢[]-cong‴ =
        let ok₁ , ok₂ , ok₃ , ok₄ , ok₅ , ⊢[]-cong″ = ⊢[]-cong″ in
        lamⱼ′ ok₁ $ lamⱼ′ ok₂ $ lamⱼ′ ok₃ $ lamⱼ′ ok₄ $
        lamⱼ′ ok₅ ⊢[]-cong″

      ▸[]-cong‴ : 𝟘ᶜ ▸[ m ] []-cong‴
      ▸[]-cong‴ =
        lamₘ $ lamₘ $ lamₘ $ lamₘ $ lamₘ $
        sub
          (▸cong (▸Erased (level var) (▸Erased (level var) var))
             (▸[] (▸[] var)) (▸[] (▸[] var)) (▸Erased (level var) var)
             (sub
                (▸mapᴱ′ trivial P-ok 𝟘≤𝟙
                   (λ _ → _ , ▸Erased (level var) var)
                   (sub
                      (▸erased′ trivial P-ok 𝟘≤𝟙 var (λ _ → _ , var))
                      (begin
                         𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
                         𝟘ᶜ                ∎))
                   var)
                (begin
                   𝟘ᶜ ∙ ⌜ m ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
                   𝟘ᶜ              ∎))
             (flip _∘ₘ_
                (▸cong var var var (▸Erased (level var) var)
                   (sub (▸[] var) $ begin
                      𝟘ᶜ ∙ ⌜ m ᵐ· 𝟘 ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
                      𝟘ᶜ                   ∎)
                   var
                   (λ _ → begin
                      𝟘ᶜ ∙ ⌜ m ᵐ· 𝟘 ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
                      𝟘ᶜ                   ∎)
                   (λ _ → begin
                      𝟘ᶜ                                             ≈˘⟨ ≈ᶜ-trans
                                                                           (+ᶜ-cong
                                                                              (≈ᶜ-trans (·ᶜ-congʳ $ ·-zeroʳ _) $
                                                                               ·ᶜ-zeroˡ _)
                                                                              (≈ᶜ-trans (+ᶜ-identityˡ _) (·ᶜ-zeroʳ _))) $
                                                                         +ᶜ-identityʳ _ ⟩
                      (⌜ m ᵐ· 𝟘 ⌝ · 𝟘) ·ᶜ (𝟘ᶜ , x2 ≔ ⌜ m ᵐ· 𝟘 ⌝) +ᶜ
                      𝟘ᶜ +ᶜ (𝟙 + 𝟙) ·ᶜ 𝟘ᶜ                            ∎)) $
              flip _∘ₘ_ (▸[] var) $
              flip _∘ₘ_ (▸[] var) $
              flip _∘ₘ_ (▸Erased (level var) var) $
              flip _∘ₘ_ var $
              wkUsage _ ▸[]-cong′)
             (λ _ → begin
                𝟘ᶜ ∙ ⌜ m ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
                𝟘ᶜ              ∎)
             (λ _ → begin
                𝟘ᶜ                                        ≈˘⟨ ≈ᶜ-trans (+ᶜ-cong (·ᶜ-zeroʳ _) (≈ᶜ-trans (+ᶜ-identityˡ _) (·ᶜ-zeroʳ _))) $
                                                              +ᶜ-identityʳ _ ⟩
                (⌜ m ⌝ · 𝟘) ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ (𝟙 + 𝟙) ·ᶜ 𝟘ᶜ  ∎)) $
        (begin
           𝟘ᶜ ∙ ⌜ m ⌝ · p₁′ ∙ ⌜ m ⌝ · p₂′ ∙ ⌜ m ⌝ · p₃′ ∙ ⌜ m ⌝ · p₄′ ∙
           ⌜ m ⌝ · 𝟘                                                     ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩

           𝟘ᶜ ∙ ⌜ m ⌝ · p₁′ ∙ ⌜ m ⌝ · p₂′ ∙ ⌜ m ⌝ · p₃′ ∙ ⌜ m ⌝ · p₄′ ∙
           𝟘                                                             ≤⟨ ≤ᶜ-refl ∙ hyp₁′ ∙ hyp₂′ ∙ hyp₃′ ∙ hyp₄′ ∙ ≤-refl ⟩

           𝟘ᶜ , x4 ≔ ⌜ m ⌝ · ω · p₁                                      ≈⟨ update-congʳ {γ = 𝟘ᶜ} {x = x4} $
                                                                            PE.trans (⌜⌝-·-comm m) $
                                                                            PE.trans (·-assoc _ _ _) $
                                                                            ·-congˡ (PE.sym (⌜⌝-·-comm m)) ⟩

           𝟘ᶜ , x4 ≔ ω · ⌜ m ⌝ · p₁                                      ≈˘⟨ ≈ᶜ-trans
                                                                               (·ᶜ-congˡ $
                                                                                ≈ᶜ-trans (+ᶜ-identityˡ _) $
                                                                                ≈ᶜ-trans (+ᶜ-identityˡ _) $
                                                                                ≈ᶜ-trans (+ᶜ-identityʳ _) $
                                                                                ≈ᶜ-trans
                                                                                  (+ᶜ-cong
                                                                                     (≈ᶜ-trans
                                                                                        (+ᶜ-cong
                                                                                           (≈ᶜ-trans
                                                                                              (+ᶜ-cong
                                                                                                 (≈ᶜ-trans
                                                                                                    (+ᶜ-cong
                                                                                                       (≈ᶜ-trans (+ᶜ-identityˡ _) $
                                                                                                        ·ᶜ𝟘ᶜ,≔⌜ᵐ·⌝ m x4)
                                                                                                       (·ᶜ-zeroʳ _)) $
                                                                                                  +ᶜ-identityʳ _)
                                                                                                 (·ᶜ-zeroʳ _)) $
                                                                                            +ᶜ-identityʳ _)
                                                                                           (·ᶜ-zeroʳ _)) $
                                                                                      +ᶜ-identityʳ _)
                                                                                     (·ᶜ-zeroˡ _)) $
                                                                                +ᶜ-identityʳ _) $
                                                                             ·ᶜ𝟘ᶜ,≔ x4 ⟩
           ω ·ᶜ
           (𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ
            (((((𝟘ᶜ +ᶜ p₁ ·ᶜ (𝟘ᶜ , x4 ≔ ⌜ m ᵐ· p₁ ⌝)) +ᶜ
                p₂ ·ᶜ 𝟘ᶜ) +ᶜ
               p₃ ·ᶜ 𝟘ᶜ) +ᶜ
              p₄ ·ᶜ 𝟘ᶜ) +ᶜ
             𝟘 ·ᶜ ω ·ᶜ
             ((𝟘ᶜ , x2 ≔ ⌜ m ᵐ· 𝟘 ⌝) +ᶜ (𝟘ᶜ , x1 ≔ ⌜ m ᵐ· 𝟘 ⌝) +ᶜ
              (𝟘ᶜ , x0 ≔ ⌜ m ᵐ· 𝟘 ⌝) +ᶜ 𝟘ᶜ)) +ᶜ
            𝟘ᶜ)                                                          ∎)
        where
        open ≤ᶜ-reasoning

private opaque

  -- Some lemmas used below.

  wk2-[]₁ : wk2 t [ sgSubst u ⇑ ] PE.≡ wk1 t
  wk2-[]₁ {t} {u} =
    wk2 t [ sgSubst u ⇑ ]        ≡⟨⟩
    wk1 (wk1 t) [ sgSubst u ⇑ ]  ≡⟨ wk1-liftSubst (wk1 t) ⟩
    wk1 (wk1 t [ u ]₀)           ≡⟨ PE.cong wk1 $ wk1-sgSubst _ _ ⟩
    wk1 t                        ∎
    where
    open Tools.Reasoning.PropositionalEquality

  wk2-[]₁[]₀ : wk2 t [ sgSubst u ⇑ ] [ v ]₀ PE.≡ t
  wk2-[]₁[]₀ {t} {u} {v} =
    wk2 t [ sgSubst u ⇑ ] [ v ]₀  ≡⟨ PE.cong _[ _ ] $ wk2-[]₁ {t = t} ⟩
    wk1 t [ v ]₀                  ≡⟨ wk1-sgSubst _ _ ⟩
    t                             ∎
    where
    open Tools.Reasoning.PropositionalEquality

  wk3-[]₂[]₁[]₀ :
    wk[ 3 ] t [ sgSubst u ⇑ ⇑ ] [ sgSubst v ⇑ ] [ w ]₀ PE.≡ t
  wk3-[]₂[]₁[]₀ {t} {u} {v} {w} =
    wk[ 3 ] t [ sgSubst u ⇑ ⇑ ] [ sgSubst v ⇑ ] [ w ]₀    ≡⟨⟩
    wk1 (wk2 t) [ sgSubst u ⇑ ⇑ ] [ sgSubst v ⇑ ] [ w ]₀  ≡⟨ PE.cong _[ _ ] $ PE.cong _[ _ ] $ wk1-liftSubst (wk2 t) ⟩
    wk1 (wk2 t [ sgSubst u ⇑ ]) [ sgSubst v ⇑ ] [ w ]₀    ≡⟨ PE.cong _[ _ ] $ wk1-liftSubst (wk2 t [ _ ]) ⟩
    wk1 (wk2 t [ sgSubst u ⇑ ] [ sgSubst v ]) [ w ]₀      ≡⟨ wk1-sgSubst _ _ ⟩
    wk2 t [ sgSubst u ⇑ ] [ sgSubst v ]                   ≡⟨ wk2-[]₁[]₀ ⟩
    t                                                     ∎
    where
    open Tools.Reasoning.PropositionalEquality

opaque
  unfolding Has-[]-cong-stronger

  -- One can replace some of the "p" grades in Has-computing-[]-cong
  -- with grades that satisfy certain assumptions (given certain
  -- assumptions).
  --
  -- Note that, if all Π-types are allowed, then all but one of the
  -- assumptions (⌜ m ⌝ · p₁′ ≤ ⌜ m ⌝ · ω · p₁) are satisfied for the
  -- erasure modality with 𝟘ᵐ.

  Has-computing-[]-cong-stronger :
    {Γ : Con Term n} →
    (s PE.≡ 𝕨 → ¬ T 𝟘ᵐ-allowed → Trivial) →
    (s PE.≡ 𝕨 → Prodrec-allowed 𝟘ᵐ? (𝟘 ∧ 𝟙) 𝟘 𝟘) →
    (s PE.≡ 𝕤 → ¬ T 𝟘ᵐ-allowed → 𝟘 ≤ 𝟙) →
    (Π-allowed p₁ q₁ → Π-allowed p₁′ q₁′) →
    (Π-allowed p₂ q₂ → Π-allowed p₂′ q₂′) →
    (Π-allowed p₃ q₃ → Π-allowed p₃′ q₃′) →
    (Π-allowed p₄ q₄ → Π-allowed p₄′ q₄′) →
    (Π-allowed 𝟘  q₅ → Π-allowed 𝟘   q₅′) →
    ⌜ m ⌝ · p₁′ ≤ ⌜ m ⌝ · ω · p₁ →
    ⌜ m ⌝ · p₂′ ≤ 𝟘 →
    ⌜ m ⌝ · p₃′ ≤ 𝟘 →
    ⌜ m ⌝ · p₄′ ≤ 𝟘 →
    Has-computing-[]-cong s m Γ p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ q₅ →
    Has-computing-[]-cong s m Γ p₁′ q₁′ p₂′ q₂′ p₃′ q₃′ p₄′ q₄′ q₅′
  Has-computing-[]-cong-stronger
    {n} {s} {p₁} {p₁′} {q₁′} {p₂} {p₂′} {q₂′} {p₃} {p₃′} {q₃′}
    {p₄} {q₄} {p₄′} {q₄′} {q₅} {q₅′} {m} {Γ}
    trivial P-ok 𝟘≤𝟙 hyp₁ hyp₂ hyp₃ hyp₄ hyp₅ hyp₁′ hyp₂′ hyp₃′ hyp₄′
    (has-[]-cong@([]-cong′ , _ , ⊢[]-cong′) , []-cong′≡) =
    has-[]-cong′ , []-cong″-computes
    where
    open Erased s

    has-[]-cong′ : Has-[]-cong s m Γ p₁′ q₁′ p₂′ q₂′ p₃′ q₃′ p₄′ q₄′ q₅′
    has-[]-cong′ =
      Has-[]-cong-stronger
        trivial P-ok 𝟘≤𝟙 hyp₁ hyp₂ hyp₃ hyp₄ hyp₅ hyp₁′ hyp₂′ hyp₃′ hyp₄′
        has-[]-cong

    []-cong″ : Term n
    []-cong″ = has-[]-cong′ .proj₁

    opaque

      lemma :
        (ρ : Wk n′ n) (l A t : Term n′) (u : Term n) →
        wk (stepn id 5) u
          U.[ consSubst
                (consSubst (consSubst (consSubst (sgSubst l) A) t) t)
                rfl ₛ•
              liftn ρ 5 ] PE.≡
        wk ρ u
      lemma ρ l A t u =
        wk (stepn id 5) u
          U.[ consSubst
                (consSubst (consSubst (consSubst (sgSubst l) A) t) t)
                rfl ₛ•
              liftn ρ 5 ]                                               ≡⟨ subst-wk u ⟩

        u U.[ (consSubst
                 (consSubst (consSubst (consSubst (sgSubst l) A) t) t)
                 rfl ₛ•
               liftn ρ 5) ₛ•
              stepn id 5 ]                                              ≡˘⟨ wk≡subst _ _ ⟩

        wk ρ u                                                          ∎
        where
        open Tools.Reasoning.PropositionalEquality

    opaque
      unfolding Erased [_]

      []-cong″-computes :
        ∀ m n′ (Δ : Cons m n′) (l A t : Term n′) (ρ : Wk n′ n) →
        Δ .defs » ρ ∷ʷ Δ .vars ⊇ Γ →
        Δ ⊢ A ∷ U (level l) →
        Δ ⊢ t ∷ A →
        Δ ⊢
          wk ρ []-cong″ ∘⟨ p₁′ ⟩ l ∘⟨ p₂′ ⟩ A ∘⟨ p₃′ ⟩ t ∘⟨ p₄′ ⟩ t
            ∘⟨ 𝟘 ⟩ rfl ≡
          rfl ∷ Id (Erased (level l) A) [ t ] ([ t ])
      []-cong″-computes _ _ Δ l A t ρ Δ⊇Γ ⊢A ⊢t =
        let open Has-[]-cong-stronger
                   hyp₁ hyp₂ hyp₃ hyp₄ hyp₅ has-[]-cong

            ok₁ , ok₂ , ok₃ , ok₄ , ok₅ , ⊢[]-cong″ = ⊢[]-cong″

            ⊇ε = WD.»⊇ε (defn-wf (wf ⊢A))
        in
        wk ρ
          (lam p₁′ $ lam p₂′ $ lam p₃′ $ lam p₄′ $ lam 𝟘 $
           cong 𝟘
             (Erased (level (var x4))
                (Erased (level (var x4)) (var x3)))
             [ [ var x2 ] ] [ [ var x1 ] ]
             (Erased (level (var x4)) (var x3))
             (mapᴱ (Erased (level (var x5)) (var x4))
                (erased (var x5) (var x0)) (var x0))
             (wk (stepn id 5) []-cong′ ∘⟨ p₁ ⟩ var x4
                ∘⟨ p₂ ⟩ Erased (level (var x4)) (var x3)
                ∘⟨ p₃ ⟩ [ var x2 ]
                ∘⟨ p₄ ⟩ [ var x1 ]
                ∘⟨ 𝟘 ⟩ cong 𝟘 (var x3) (var x2) (var x1)
                         (Erased (level (var x4)) (var x3)) [ var x0 ]
                         (var x0)))
          ∘⟨ p₁′ ⟩ l ∘⟨ p₂′ ⟩ A ∘⟨ p₃′ ⟩ t ∘⟨ p₄′ ⟩ t ∘⟨ 𝟘 ⟩ rfl ∷
          Id (Erased (level l) A) [ t ] ([ t ])                         ⇒*⟨ β-red-⇒₅′ ok₁ ok₂ ok₃ ok₄ ok₅
                                                                              (W.wk
                                                                                 (W.liftnʷ Δ⊇Γ $
                                                                                  ∙ ⊢Id-2-1-0 Level-ok (WD.defn-wk ⊇ε (wf ⊢[]-cong′))) $
                                                                               WD.defn-wk ⊇ε ⊢[]-cong″)
                                                                              ⊢l ⊢A ⊢t ⊢t (rflⱼ ⊢t) ⟩⊢∷
                                                                         ˘⟨ Id-cong (refl (univ ⊢Erased-A)) mapᴱ-lemma mapᴱ-lemma ⟩≡
        wk (liftn ρ 5)
          (cong 𝟘
             (Erased (level (var x4))
                (Erased (level (var x4)) (var x3)))
             [ [ var x2 ] ] [ [ var x1 ] ]
             (Erased (level (var x4)) (var x3))
             (mapᴱ (Erased (level (var x5)) (var x4))
                (erased (var x5) (var x0)) (var x0))
             (wk (stepn id 5) []-cong′ ∘⟨ p₁ ⟩ var x4
                ∘⟨ p₂ ⟩ Erased (level (var x4)) (var x3)
                ∘⟨ p₃ ⟩ [ var x2 ]
                ∘⟨ p₄ ⟩ [ var x1 ]
                ∘⟨ 𝟘 ⟩ cong 𝟘 (var x3) (var x2) (var x1)
                         (Erased (level (var x4)) (var x3)) [ var x0 ]
                         (var x0)))
          U.[ consSubst
                (consSubst (consSubst (consSubst (sgSubst l) A) t) t)
                rfl ] ∷
          Id (Erased (level l) A)
            (mapᴱ (Erased (level (wk1 l)) (wk1 A))
               (erased (wk2 A) (var x0)) (var x0) [ [ [ t ] ] ]₀)
            (mapᴱ (Erased (level (wk1 l)) (wk1 A))
               (erased (wk2 A) (var x0)) (var x0) [ [ [ t ] ] ]₀)       ≡⟨ PE.trans (subst-wk (cong _ _ _ _ _ _ _)) $
                                                                           PE.trans cong-[] $
                                                                           PE.cong₂ (cong _ _ _ _ _)
                                                                             (PE.trans mapᴱ-[] $
                                                                              PE.cong₂ (mapᴱ _) erased-[] PE.refl)
                                                                             (PE.cong₂ _∘⟨ 𝟘 ⟩_
                                                                                (PE.cong (_∘⟨ p₄ ⟩ [ t ]) $
                                                                                 PE.cong (_∘⟨ p₃ ⟩ [ t ]) $
                                                                                 PE.cong (_∘⟨ p₂ ⟩ Erased (level l) A) $
                                                                                 PE.cong (_∘⟨ _ ⟩ _) $
                                                                                 lemma _ _ _ _ _)
                                                                                cong-[]) ⟩⊢∷≡
        cong 𝟘 (Erased (level l) (Erased (level l) A)) [ [ t ] ]
          [ [ t ] ] (Erased (level l) A)
          (mapᴱ (Erased (level (wk1 l)) (wk1 A))
             (erased (wk2 A) (var x0)) (var x0))
          (wk ρ []-cong′ ∘⟨ p₁ ⟩ l ∘⟨ p₂ ⟩ Erased (level l) A
             ∘⟨ p₃ ⟩ [ t ] ∘⟨ p₄ ⟩ [ t ]
             ∘⟨ 𝟘 ⟩ cong 𝟘 A t t (Erased (level l) A) [ var x0 ] rfl)   ≡⟨ cong-cong (refl ⊢Erased-Erased-A) (refl ⊢[[t]]) (refl ⊢[[t]])
                                                                             (refl (univ ⊢Erased-A)) (refl ⊢mapᴱ-0) $
                                                                           PE.subst (_⊢_≡_∷_ _ _ _)
                                                                             (PE.cong₃ Id ≡Erased-Erased wk2-[]₁[]₀ (wk1-sgSubst _ _)) $
                                                                           _⊢_≡_∷_.app-cong
                                                                             (_⊢_≡_∷_.refl $
                                                                              PE.subst (_⊢_∷_ _ _)
                                                                                (PE.cong₂ (Π_,_▷_▹_ 𝟘 q₅)
                                                                                   (PE.cong₃ Id wk2-[]₁[]₀ (wk1-sgSubst _ _) PE.refl) $
                                                                                 PE.refl) $
                                                                              flip _∘ⱼ_ ⊢[t] $
                                                                              PE.subst (_⊢_∷_ _ _)
                                                                                (PE.cong₂ (Π_,_▷_▹_ p₄ q₄) (wk1-sgSubst _ _) PE.refl) $
                                                                              flip _∘ⱼ_ ⊢[t] $
                                                                              flip _∘ⱼ_ ⊢Erased-A∷U $
                                                                              flip _∘ⱼ_ ⊢l $
                                                                              W.wk Δ⊇Γ $
                                                                              WD.defn-wk ⊇ε ⊢[]-cong′) $
                                                                           cong-≡ ⊢t $
                                                                           PE.subst (_⊢_∷_ _ _) (PE.sym wk-Erased) $
                                                                           []ⱼ Erased-ok (W.wk₁ (univ ⊢A) ⊢l∷L) (var₀ (univ ⊢A)) ⟩⊢
        cong 𝟘 (Erased (level l) (Erased (level l) A)) [ [ t ] ]
          [ [ t ] ] (Erased (level l) A)
          (mapᴱ (Erased (level (wk1 l)) (wk1 A))
             (erased (wk2 A) (var x0)) (var x0))
          (wk ρ []-cong′ ∘⟨ p₁ ⟩ l ∘⟨ p₂ ⟩ Erased (level l) A
             ∘⟨ p₃ ⟩ [ t ] ∘⟨ p₄ ⟩ [ t ] ∘⟨ 𝟘 ⟩ rfl)                    ≡⟨ cong-cong (refl ⊢Erased-Erased-A) (refl ⊢[[t]]) (refl ⊢[[t]])
                                                                             (refl (univ ⊢Erased-A)) (refl ⊢mapᴱ-0) $
                                                                           []-cong′≡ _ _ _ _ _ _ _ Δ⊇Γ ⊢Erased-A∷U ⊢[t] ⟩⊢
        cong 𝟘 (Erased (level l) (Erased (level l) A)) [ [ t ] ]
          [ [ t ] ] (Erased (level l) A)
          (mapᴱ (Erased (level (wk1 l)) (wk1 A))
             (erased (wk2 A) (var x0)) (var x0))
          rfl                                                           ⇒⟨ cong-⇒ ⊢[[t]] ⊢mapᴱ-0 ⟩⊢∎

        rfl                                                             ∎
        where
        Level-ok : Level-allowed
        Level-ok = Has-[]-cong→Level-allowed has-[]-cong

        Erased-ok : Erased-allowed s
        Erased-ok =
          proj₁ $ inversion-Erased $
          proj₁ $ inversion-Id $
          proj₁ $ proj₂ $ inversion-ΠΣ $
          proj₁ $ proj₂ $ inversion-ΠΣ $
          proj₁ $ proj₂ $ inversion-ΠΣ $
          proj₁ $ proj₂ $ inversion-ΠΣ $
          proj₁ $ proj₂ $ inversion-ΠΣ $
          wf-⊢ $ has-[]-cong′ .proj₂ .proj₂

        ⊢l∷L : Δ ⊢ level l ∷Level
        ⊢l∷L = inversion-U-Level (wf-⊢ ⊢A)

        ⊢l : Δ ⊢ l ∷ Level
        ⊢l = ⊢∷Level→⊢∷Level Level-ok ⊢l∷L

        ⊢[t] : Δ ⊢ [ t ] ∷ Erased (level l) A
        ⊢[t] = []ⱼ Erased-ok ⊢l∷L ⊢t

        ⊢Erased-A : Δ ⊢ Erased (level l) A ∷ U (level l)
        ⊢Erased-A = Erasedⱼ-U Erased-ok ⊢A

        ⊢[[t]] : Δ ⊢ [ [ t ] ] ∷ Erased (level l) (Erased (level l) A)
        ⊢[[t]] = []ⱼ Erased-ok ⊢l∷L ⊢[t]

        ⊢Erased-Erased-A : Δ ⊢ Erased (level l) (Erased (level l) A)
        ⊢Erased-Erased-A = wf-⊢ ⊢[[t]]

        ⊢Erased-A∷U : Δ ⊢ Erased (level l) A ∷ U (level l)
        ⊢Erased-A∷U = Erasedⱼ-U Erased-ok ⊢A

        ⊢mapᴱ-0 :
          Δ »∙ Erased (level l) (Erased (level l) A) ⊢
            mapᴱ (Erased (level (wk1 l)) (wk1 A))
              (erased (wk2 A) (var x0)) (var x0) ∷
            wk1 (Erased (level l) A)
        ⊢mapᴱ-0 =
          PE.subst (_⊢_∷_ _ _) (PE.sym wk-Erased) $
          ⊢mapᴱ (W.wk₁ ⊢Erased-Erased-A ⊢l∷L)
            (erasedⱼ $ PE.subst (_⊢_∷_ _ _) wk-Erased $
             var₀ $ PE.subst (_⊢_ _) wk-Erased $
             W.wk₁ ⊢Erased-Erased-A (univ ⊢Erased-A))
            (PE.subst (_⊢_∷_ _ _)
               (PE.trans wk-Erased $ PE.cong (Erased _) wk-Erased) $
             var₀ ⊢Erased-Erased-A)

        mapᴱ-lemma :
          Δ ⊢
            mapᴱ (Erased (level (wk1 l)) (wk1 A))
              (erased (wk2 A) (var x0)) (var x0) [ [ [ t ] ] ]₀ ≡
            [ t ] ∷
            Erased (level l) A
        mapᴱ-lemma =
          mapᴱ (Erased (level (wk1 l)) (wk1 A))
            (erased (wk2 A) (var x0)) (var x0) [ [ [ t ] ] ]₀  ≡⟨ PE.trans mapᴱ-[] $
                                                                  PE.cong₃ mapᴱ
                                                                    (PE.trans
                                                                       (PE.cong _[ [ [ t ] ] ]₀ $ PE.sym $
                                                                        wk-Erased {l = level l} {A = A}) $
                                                                     wk1-sgSubst _ _)
                                                                    (PE.trans erased-[] $
                                                                     PE.cong₂ erased wk2-[]₁ PE.refl)
                                                                    PE.refl ⟩⊢≡

          mapᴱ (Erased (level l) A) (erased (wk1 A) (var x0))
            ([ [ t ] ])                                        ≡⟨ mapᴱ-β Erased-ok ⊢l∷L
                                                                    (erasedⱼ $
                                                                     PE.subst (_⊢_∷_ _ _) wk-Erased $
                                                                     var₀ (univ ⊢Erased-A))
                                                                    ([]ⱼ Erased-ok ⊢l∷L ⊢t) ⟩⊢

          [ erased (wk1 A) (var x0) [ [ t ] ]₀ ]               ≡⟨ PE.cong ([_]) $
                                                                  PE.trans erased-[] $
                                                                  PE.cong₂ erased (wk1-sgSubst _ _) PE.refl ⟩⊢≡

          [ erased A ([ t ]) ]                                 ≡⟨ P.[]-cong′ Erased-ok ⊢l∷L $
                                                                  Erased-β Erased-ok ⊢t ⟩⊢∎
          [ t ]                                                ∎

        ≡Erased-Erased :
          (Σ⟨ s ⟩ 𝟘 , 𝟘 ▷
           wk[ 3 ] (Erased (level l) A) ▹
           Lift
             (wk[ 5 ] (level l)
                U.[ sgSubst (Erased (level l) A) ⇑[ 4 ] ])
             (Unit s))
            U.[ sgSubst ([ t ]) ⇑[ 2 ] ] [ sgSubst ([ t ]) ⇑ ]
            [ cong 𝟘 A t t (Erased (level l) A) [ var x0 ] rfl ]₀ PE.≡
          Erased (level l) (Erased (level l) A)
        ≡Erased-Erased =
          let u = cong 𝟘 A t t (Erased (level l) A) [ var x0 ] rfl

              lemma =
                wk[ 5 ] (level l)
                  U.[ sgSubst (Erased (level l) A) ⇑[ 4 ] ]  ≡⟨ PE.cong _[ sgSubst (Erased (level l) A) ⇑[ 4 ] ] $ wk[]≡wk[]′ {t = level l} ⟩

                wk[ 5 ]′ (level l)
                  U.[ sgSubst (Erased (level l) A) ⇑[ 4 ] ]  ≡⟨ wk[+1]′-[₀⇑]≡ ⟩

                wk[ 4 ]′ (level l)                           ≡˘⟨ wk[]≡wk[]′ ⟩

                wk[ 4 ] (level l)                            ∎
          in

          (Σ⟨ s ⟩ 𝟘 , 𝟘 ▷
           wk[ 3 ] (Erased (level l) A) ▹
           Lift
             (wk[ 5 ] (level l)
                U.[ sgSubst (Erased (level l) A) ⇑[ 4 ] ])
             (Unit s))
            U.[ sgSubst ([ t ]) ⇑[ 2 ] ] [ sgSubst ([ t ]) ⇑ ] [ u ]₀  ≡⟨ PE.cong _[ u ]₀ $ PE.cong _[ sgSubst ([ t ]) ⇑ ] $
                                                                          PE.cong _[ sgSubst ([ t ]) ⇑[ 2 ] ] $
                                                                          PE.cong (Σ⟨ s ⟩ 𝟘 , 𝟘 ▷ wk[ 3 ] (Erased (level l) A) ▹_) $
                                                                          PE.cong (flip Lift (Unit s)) lemma ⟩
          Erased (wk[ 3 ] (level l)) (wk[ 3 ] (Erased (level l) A))
            U.[ sgSubst ([ t ]) ⇑[ 2 ] ] [ sgSubst ([ t ]) ⇑ ] [ u ]₀  ≡˘⟨ PE.cong (_[ u ]₀ ∘→ _[ sgSubst ([ t ]) ⇑ ]) $
                                                                           PE.cong _[ sgSubst ([ t ]) ⇑[ 2 ] ] $
                                                                           PE.trans wk[]≡wk[]′ $
                                                                           PE.trans (wk-Erased {l = level l} {A = Erased (level l) A}) $
                                                                           PE.sym $ PE.cong₂ Erased wk[]≡wk[]′ wk[]≡wk[]′ ⟩
          wk[ 3 ] (Erased (level l) (Erased (level l) A))
            U.[ sgSubst ([ t ]) ⇑[ 2 ] ] [ sgSubst ([ t ]) ⇑ ] [ u ]₀  ≡⟨ wk3-[]₂[]₁[]₀ ⟩

          Erased (level l) (Erased (level l) A)                        ∎
          where
          open Tools.Reasoning.PropositionalEquality
