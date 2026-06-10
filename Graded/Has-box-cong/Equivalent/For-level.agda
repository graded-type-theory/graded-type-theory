------------------------------------------------------------------------
-- Some instances of
-- Has-[]-cong-for-level/Has-computing-[]-cong-for-level are logically
-- equivalent
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
import Graded.Modality
import Graded.Mode.Instances.Zero-one
open import Graded.Mode.Instances.Zero-one.Variant
open import Graded.Usage.Restrictions

module Graded.Has-box-cong.Equivalent.For-level
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
open import Definition.Typed.Decidable.Internal Zero-one-isMode TR
import Definition.Typed.Decidable.Internal.Context Zero-one-isMode TR
  as IC
import Definition.Typed.Decidable.Internal.Substitution
  Zero-one-isMode TR as IS
import Definition.Typed.Decidable.Internal.Term Zero-one-isMode TR as I
import Definition.Typed.Decidable.Internal.Weakening Zero-one-isMode TR
  as IW
open import Definition.Typed.Inversion TR
open import Definition.Typed.Properties TR
open import Definition.Typed.Reasoning.Term TR
open import Definition.Typed.Weakening TR as W using (_»_∷ʷ_⊇_)
import Definition.Typed.Weakening.Definition TR as WD
open import Definition.Typed.Well-formed TR
open import Definition.Untyped M as U
import Definition.Untyped.Erased 𝕄 as Erased
open import Definition.Untyped.Identity 𝕄 as UI
open import Definition.Untyped.Properties M
open import Definition.Untyped.Sigma 𝕄

open UI.Internal Zero-one-isMode TR

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

open import Tools.Bool using (T; true)
open import Tools.Fin
open import Tools.Function
import Tools.List as L
open import Tools.Maybe
open import Tools.Nat using (Nat; 4+)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation
import Tools.Vec as V

private variable
  n n₁ n₂                                          : Nat
  Δ                                                : Con Term _
  l                                                : Lvl _
  sᵢ                                               : I.Termˢ _
  p₁ p₁′ p₂ p₂′ p₃ p₃′ q₁ q₁′ q₂ q₂′ q₃ q₃′ q₄ q₄′ : M
  γ                                                : Conₘ _
  m                                                : Mode
  s                                                : Strength

------------------------------------------------------------------------
-- Some instances of
-- Has-[]-cong-for-level/Has-computing-[]-cong-for-level are logically
-- equivalent

-- Some definitions/lemmas used below.

private
  module Has-[]-cong-for-level-weaker
    {Γ : Con Term n}
    (hyp₁ : Π-allowed p₁ q₁ → Π-allowed p₁′ q₁′)
    (hyp₂ : Π-allowed p₂ q₂ → Π-allowed p₂′ q₂′)
    (hyp₃ : Π-allowed p₃ q₃ → Π-allowed p₃′ q₃′)
    (hyp₄ : Π-allowed 𝟘  q₄ → Π-allowed 𝟘   q₄′)
    (has-[]-cong@([]-cong′ , _ , ⊢[]-cong′) :
     Has-[]-cong-for-level s m Γ l p₁ q₁ p₂ q₂ p₃ q₃ q₄)
    where

    open Erased s

    []-cong″ : Term (4+ n)
    []-cong″ =
       wk (stepn id 4) []-cong′ ∘⟨ p₁ ⟩ var x3 ∘⟨ p₂ ⟩ var x2
         ∘⟨ p₃ ⟩ var x1 ∘⟨ 𝟘 ⟩ var x0

    opaque
      unfolding Erased [_]

      ⊢[]-cong″ :
        ε » Γ ∙ U l ∙ var x0 ∙ var x1 ∙ Id (var x2) (var x1) (var x0) ⊢
          []-cong″ ∷
          Id (Erased (wk[ 4 ]′ l) (var x3)) [ var x2 ] ([ var x1 ])
      ⊢[]-cong″ =
        PE.subst (_⊢_∷_ _ _)
          (PE.cong₃ Id
             (PE.cong (Σ⟨ s ⟩ 𝟘 , 𝟘 ▷_▹_ _ ∘→ flip Lift _) $
              PE.trans
                (substCompEq
                   (wk _ (wk1 (wk[ 4 ]′ l)) U.[ _ ] U.[ _ ])) $
              PE.trans (substCompEq (wk _ (wk1 (wk[ 4 ]′ l)) U.[ _ ])) $
              PE.trans (substCompEq (wk _ (wk1 (wk[ 4 ]′ l)))) $
              PE.trans (subst-wk (wk1 (wk[ 4 ]′ l))) $
              PE.trans
                (flip substVar-to-subst (wk1 (wk[ 4 ]′ l)) λ where
                   x0                  → PE.refl
                   (x0 +1)             → PE.refl
                   (x0 +1 +1)          → PE.refl
                   (x0 +1 +1 +1)       → PE.refl
                   (x0 +1 +1 +1 +1)    → PE.refl
                   (_  +1 +1 +1 +1 +1) → PE.refl) $
              subst-id _)
             PE.refl PE.refl) $
        flip _∘ⱼ_ (var₀ ⊢Id) $
        flip _∘ⱼ_ (var₁ ⊢Id) $
        flip _∘ⱼ_ (var₂ ⊢Id) $
        flip _∘ⱼ_ (var₃ ⊢Id) $
        PE.subst (_⊢_∷_ _ _)
          (PE.cong₂ (Π p₁ , q₁ ▷_▹_)
             (PE.cong U (PE.sym wk[]≡wk[]′)) PE.refl) $
        WD.defn-wk (WD.»⊇ε ε) $
        W.wk (W.ʷ⊇-drop (∙ ⊢Id)) ⊢[]-cong′
        where
        ⊢Id :
          ε » Γ ∙ U l ∙ var x0 ∙ var x1 ⊢ Id (var x2) (var x1) (var x0)
        ⊢Id = ⊢Id-2-1-0′ (Has-[]-cong-for-level→⊢∷L has-[]-cong)

    oks :
      Π-allowed p₁′ q₁′ × Π-allowed p₂′ q₂′ × Π-allowed p₃′ q₃′ ×
      Π-allowed 𝟘 q₄′
    oks =
      let _ , ⊢Π , ok₁ = inversion-ΠΣ $ wf-⊢ ⊢[]-cong′
          _ , ⊢Π , ok₂ = inversion-ΠΣ ⊢Π
          _ , ⊢Π , ok₃ = inversion-ΠΣ ⊢Π
          _ , _  , ok₄ = inversion-ΠΣ ⊢Π
      in
      hyp₁ ok₁ , hyp₂ ok₂ , hyp₃ ok₃ , hyp₄ ok₄

opaque

  -- One can make the "p" grades of Has-[]-cong-for-level "smaller"
  -- (given certain assumptions).

  Has-[]-cong-for-level-weaker :
    {Γ : Con Term n} →
    (Π-allowed p₁ q₁ → Π-allowed p₁′ q₁′) →
    (Π-allowed p₂ q₂ → Π-allowed p₂′ q₂′) →
    (Π-allowed p₃ q₃ → Π-allowed p₃′ q₃′) →
    (Π-allowed 𝟘  q₄ → Π-allowed 𝟘   q₄′) →
    ⌜ m ⌝ · p₁′ ≤ ⌜ m ⌝ · p₁ →
    ⌜ m ⌝ · p₂′ ≤ ⌜ m ⌝ · p₂ →
    ⌜ m ⌝ · p₃′ ≤ ⌜ m ⌝ · p₃ →
    Has-[]-cong-for-level s m Γ l p₁ q₁ p₂ q₂ p₃ q₃ q₄ →
    Has-[]-cong-for-level s m Γ l p₁′ q₁′ p₂′ q₂′ p₃′ q₃′ q₄′
  Has-[]-cong-for-level-weaker
    {n} {p₁} {p₁′} {q₁′} {p₂} {p₂′} {q₂′} {p₃} {p₃′} {q₃′} {q₄′} {m} {s}
    {l} {Γ}
    hyp₁ hyp₂ hyp₃ hyp₄ hyp₁′ hyp₂′ hyp₃′
    has-[]-cong@(_ , ▸[]-cong′ , _) =
    []-cong‴ , ▸[]-cong‴ , ⊢[]-cong‴
    where
    open Erased s
    open Has-[]-cong-for-level-weaker hyp₁ hyp₂ hyp₃ hyp₄ has-[]-cong

    []-cong‴ : Term n
    []-cong‴ = lam p₁′ $ lam p₂′ $ lam p₃′ $ lam 𝟘 []-cong″

    ▸[]-cong‴ : 𝟘ᶜ ▸[ m ] []-cong‴
    ▸[]-cong‴ =
      lamₘ $ lamₘ $ lamₘ $ lamₘ $
      sub
        ((((wkUsage (stepn id 4) ▸[]-cong′ ∘ₘ var) ∘ₘ var) ∘ₘ var) ∘ₘ
         var) $
      (begin
         𝟘ᶜ ∙ ⌜ m ⌝ · p₁′ ∙ ⌜ m ⌝ · p₂′ ∙ ⌜ m ⌝ · p₃′ ∙ ⌜ m ⌝ · 𝟘  ≤⟨ ≤ᶜ-refl ∙ hyp₁′ ∙ hyp₂′ ∙ hyp₃′ ∙ ≤-reflexive (·-zeroʳ _) ⟩

         𝟘ᶜ ∙ ⌜ m ⌝ · p₁ ∙ ⌜ m ⌝ · p₂ ∙ ⌜ m ⌝ · p₃ ∙ 𝟘             ≈˘⟨ (≈ᶜ-trans (+ᶜ-congˡ (·ᶜ-zeroˡ _)) $
                                                                       ≈ᶜ-trans (+ᶜ-identityʳ _) $
                                                                       ≈ᶜ-trans
                                                                         (+ᶜ-cong
                                                                            (+ᶜ-cong
                                                                               (≈ᶜ-trans (+ᶜ-identityˡ _) (·ᶜ𝟘ᶜ,≔⌜ᵐ·⌝ m x3))
                                                                               (·ᶜ𝟘ᶜ,≔⌜ᵐ·⌝ m x2))
                                                                            (·ᶜ𝟘ᶜ,≔⌜ᵐ·⌝ m x1))
                                                                         ((≈ᶜ-trans (+ᶜ-identityʳ _) $
                                                                           +ᶜ-identityʳ _) ∙
                                                                          (PE.trans (+-identityʳ _) $
                                                                           +-identityʳ _) ∙
                                                                          (PE.trans (+-identityʳ _) $
                                                                           +-identityˡ _) ∙
                                                                          (PE.trans (+-congʳ (+-identityʳ _)) $
                                                                           +-identityˡ _) ∙
                                                                          (PE.trans (+-identityʳ _) $
                                                                           +-identityʳ _))) ⟩
         (((𝟘ᶜ +ᶜ p₁ ·ᶜ (𝟘ᶜ , x3 ≔ ⌜ m ᵐ· p₁ ⌝)) +ᶜ
           p₂ ·ᶜ (𝟘ᶜ , x2 ≔ ⌜ m ᵐ· p₂ ⌝)) +ᶜ
          p₃ ·ᶜ (𝟘ᶜ , x1 ≔ ⌜ m ᵐ· p₃ ⌝)) +ᶜ
         𝟘 ·ᶜ (𝟘ᶜ , x0 ≔ ⌜ m ᵐ· 𝟘 ⌝)                               ∎)
      where
      open ≤ᶜ-reasoning

    ⊢[]-cong‴ :
      ε » Γ ⊢ []-cong‴ ∷
        Π p₁′ , q₁′ ▷ U l ▹
        Π p₂′ , q₂′ ▷ var x0 ▹
        Π p₃′ , q₃′ ▷ var x1 ▹
        Π 𝟘   , q₄′ ▷ Id (var x2) (var x1) (var x0) ▹
        Id (Erased (wk[ 4 ]′ l) (var x3)) ([ var x2 ]) ([ var x1 ])
    ⊢[]-cong‴ =
      let ok₁ , ok₂ , ok₃ , ok₄ = oks in
      lamⱼ′ ok₁ $ lamⱼ′ ok₂ $ lamⱼ′ ok₃ $ lamⱼ′ ok₄ ⊢[]-cong″

opaque
  unfolding Has-[]-cong-for-level-weaker Erased.Erased Erased.[_]

  -- One can make the "p" grades of Has-computing-[]-cong-for-level
  -- "smaller" (given certain assumptions).

  Has-computing-[]-cong-for-level-weaker :
    (Π-allowed p₁ q₁ → Π-allowed p₁′ q₁′) →
    (Π-allowed p₂ q₂ → Π-allowed p₂′ q₂′) →
    (Π-allowed p₃ q₃ → Π-allowed p₃′ q₃′) →
    (Π-allowed 𝟘  q₄ → Π-allowed 𝟘   q₄′) →
    ⌜ m ⌝ · p₁′ ≤ ⌜ m ⌝ · p₁ →
    ⌜ m ⌝ · p₂′ ≤ ⌜ m ⌝ · p₂ →
    ⌜ m ⌝ · p₃′ ≤ ⌜ m ⌝ · p₃ →
    Has-computing-[]-cong-for-level s m Δ l p₁ q₁ p₂ q₂ p₃ q₃ q₄ →
    Has-computing-[]-cong-for-level s m Δ l p₁′ q₁′ p₂′ q₂′ p₃′ q₃′ q₄′
  Has-computing-[]-cong-for-level-weaker
    {p₁} {p₁′} {p₂} {p₂′} {p₃} {p₃′} {s} {l}
    hyp₁ hyp₂ hyp₃ hyp₄ hyp₁′ hyp₂′ hyp₃′
    (has-[]-cong@([]-cong′ , _ , ⊢[]-cong′) , []-cong′≡) =
    let ⊢l                    = Has-[]-cong-for-level→⊢∷L has-[]-cong
        ok₁ , ok₂ , ok₃ , ok₄ = oks
    in
      Has-[]-cong-for-level-weaker hyp₁ hyp₂ hyp₃ hyp₄ hyp₁′ hyp₂′ hyp₃′
        has-[]-cong
    , λ _ _ _ A t ρ Δ⊇Γ ⊢A ⊢t →
        let ⊇ε = WD.»⊇ε (defn-wf (wf ⊢A)) in
        wk ρ
          (lam p₁′ $ lam p₂′ $ lam p₃′ $ lam 𝟘 $
           wk (stepn id 4) []-cong′ ∘⟨ p₁ ⟩ var x3 ∘⟨ p₂ ⟩ var x2
             ∘⟨ p₃ ⟩ var x1 ∘⟨ 𝟘 ⟩ var x0)
          ∘⟨ p₁′ ⟩ A ∘⟨ p₂′ ⟩ t ∘⟨ p₃′ ⟩ t ∘⟨ 𝟘 ⟩ rfl                     ⇒*⟨ PE.subst (_⊢_⇒*_∷_ _ _ _)
                                                                                (PE.cong₃ Id
                                                                                   (PE.cong (Σ⟨ s ⟩ 𝟘 , 𝟘 ▷_▹_ _ ∘→ flip Lift _) $
                                                                                    PE.trans (subst-wk (wk1 (wk[ 4 ]′ l))) $
                                                                                    PE.trans (subst-wk (wk[ 4 ]′ l)) $
                                                                                    PE.trans (subst-wk l) $
                                                                                    PE.sym $
                                                                                    PE.trans (wk-comp _ _ _) $
                                                                                    wk≡subst _ _)
                                                                                   PE.refl PE.refl) $
                                                                              β-red-⇒₄′ ok₁ ok₂ ok₃ ok₄
                                                                                (W.wk (W.liftnʷ Δ⊇Γ (∙ (⊢Id-2-1-0′ (WD.defn-wk ⊇ε ⊢l)))) $
                                                                                 WD.defn-wk ⊇ε ⊢[]-cong″)
                                                                                ⊢A ⊢t ⊢t (rflⱼ ⊢t) ⟩⊢
        (wk (liftn ρ 4) (wk (stepn id 4) []-cong′)
           [ consSubst (consSubst (consSubst (sgSubst A) t) t) rfl ])
          ∘⟨ p₁ ⟩ A ∘⟨ p₂ ⟩ t ∘⟨ p₃ ⟩ t ∘⟨ 𝟘 ⟩ rfl                        ≡⟨ PE.cong (λ []-cong → []-cong ∘⟨ _ ⟩ _ ∘⟨ _ ⟩ _ ∘⟨ _ ⟩ _ ∘⟨ _ ⟩ _) $
                                                                             PE.trans (subst-wk (wk[ 4 ]′ []-cong′)) $
                                                                             PE.trans (subst-wk []-cong′) $
                                                                             PE.sym (wk≡subst _ _) ⟩⊢≡

        wk ρ []-cong′ ∘⟨ p₁ ⟩ A ∘⟨ p₂ ⟩ t ∘⟨ p₃ ⟩ t ∘⟨ 𝟘 ⟩ rfl            ≡⟨ []-cong′≡ _ _ _ _ _ _ Δ⊇Γ ⊢A ⊢t ⟩⊢∎

        rfl                                                               ∎
    where
    open Has-[]-cong-for-level-weaker hyp₁ hyp₂ hyp₃ hyp₄ has-[]-cong

-- Some definitions/lemmas used below.

private
  module Has-[]-cong-for-level-stronger
    {Γ : Con Term n}
    (hyp₁ : Π-allowed p₁ q₁ → Π-allowed p₁′ q₁′)
    (hyp₂ : Π-allowed p₂ q₂ → Π-allowed p₂′ q₂′)
    (hyp₃ : Π-allowed p₃ q₃ → Π-allowed p₃′ q₃′)
    (hyp₄ : Π-allowed 𝟘  q₄ → Π-allowed 𝟘   q₄′)
    (has-[]-cong@([]-cong′ , _ , ⊢[]-cong′) :
     Has-[]-cong-for-level s m Γ l p₁ q₁ p₂ q₂ p₃ q₃ q₄)
    where

    open Erased s
    open Erased.Internal s Zero-one-isMode TR hiding (sᵢ)

    []-cong″ : Term n
    []-cong″ =
      lam p₁′ $ lam p₂′ $ lam p₃′ $ lam 𝟘 $
      cong 𝟘 (Erased (wk[ 4 ]′ l) (Erased (wk[ 4 ]′ l) (var x3)))
        [ [ var x2 ] ] [ [ var x1 ] ] (Erased (wk[ 4 ]′ l) (var x3))
        (mapᴱ (Erased (wk[ 5 ]′ l) (var x4))
           (erased (var x5) (var x0)) (var x0))
        (wk[ 4 ]′ []-cong′ ∘⟨ p₁ ⟩ Erased (wk[ 4 ]′ l) (var x3)
           ∘⟨ p₂ ⟩ [ var x2 ] ∘⟨ p₃ ⟩ [ var x1 ]
           ∘⟨ 𝟘 ⟩ cong 𝟘 (var x3) (var x2) (var x1)
                    (Erased (wk[ 4 ]′ l) (var x3)) [ var x0 ] (var x0))

    opaque

      Erased-ok : Erased-allowed s
      Erased-ok = Has-[]-cong-for-level→Erased-allowed has-[]-cong

    module Box-cong-internal
      (Δ : Cons n₁ n₂) (l : Lvl n₂) ([]-cong′ A t : Term n₂)
      (⊢l : Δ ⊢ l ∷Level)
      (⊢[]-cong′ :
         Δ ⊢ []-cong′ ∷
         Π p₁ , q₁ ▷ U l ▹
         Π p₂ , q₂ ▷ var x0 ▹
         Π p₃ , q₃ ▷ var x1 ▹
         Π 𝟘  , q₄ ▷ Id (var x2) (var x1) (var x0) ▹
         Id (Erased (wk[ 4 ]′ l) (var x3)) ([ var x2 ]) ([ var x1 ]))
      (⊢A : Δ ⊢ A ∷ U l)
      (⊢t : Δ ⊢ t ∷ A)
      where

      c : I.Constants
      c .I.gs                 = 14
      c .I.ss                 = 0
      c .I.bms                = 0
      c .I.ms                 = 4
      c .I.base-dcon-size     = n₁
      c .I.base-con-size      = n₂
      c .I.base-con-allowed   = true
      c .I.meta-con-size      = V.replicate 4 n₂
      c .I.meta-con-term-kind = lvl V.∷ V.replicate 3 tm

      xp₁ xp₁′ xp₂ xp₂′ xp₃ xp₃′ xq₁ xq₁′ xq₂ xq₂′ xq₃ xq₃′ xq₄ xq₄′ :
        I.Termᵍ 14
      xp₁  = I.var x0
      xp₁′ = I.var x1
      xp₂  = I.var x2
      xp₂′ = I.var x3
      xp₃  = I.var x4
      xp₃′ = I.var x5
      xq₁  = I.var x6
      xq₁′ = I.var x7
      xq₂  = I.var x8
      xq₂′ = I.var x9
      xq₃  = I.var x10
      xq₃′ = I.var x11
      xq₄  = I.var (x11 +1)
      xq₄′ = I.var (x11 +1 +1)

      xl : I.Lvl c n₂
      xl = I.varᵐ x0

      x[]-cong xA xt : I.Term c n₂
      x[]-cong = I.varᵐ x1
      xA       = I.varᵐ x2
      xt       = I.varᵐ x3

      γ′ : I.Termˢ 0 → I.Contexts c
      γ′ _ .I.grades =
        p₁ V.∷ p₁′ V.∷ p₂ V.∷ p₂′ V.∷ p₃ V.∷ p₃′ V.∷ q₁ V.∷ q₁′ V.∷
        q₂ V.∷ q₂′ V.∷ q₃ V.∷ q₃′ V.∷ q₄ V.∷ q₄′ V.∷ V.ε
      γ′ _ .I.strengths    = V.ε
      γ′ _ .I.binder-modes = V.ε
      γ′ _ .I.⌜base⌝       = Δ
      γ′ _ .I.constraints⁰ = I.emptyᶜ⁰
      γ′ s .I.constraints⁺ =
        I.unit-allowed s      L.∷
        I.σ-allowed s I.𝟘 I.𝟘 L.∷
        I.π-allowed xp₁′ xq₁′ L.∷
        I.π-allowed xp₂′ xq₂′ L.∷
        I.π-allowed xp₃′ xq₃′ L.∷
        I.π-allowed I.𝟘  xq₄′ L.∷
        L.[]
      γ′ _ .I.metas .I.equalities = L.[]
      γ′ s .I.metas .I.bindings   = λ where
        (I.var! x0) → I.base , I.level l
        (I.var! x1) →
          I.base ,
          I.term
            []-cong′
            (I.Π xp₁ , xq₁ ▷ I.U xl ▹
             I.Π xp₂ , xq₂ ▷ I.var x0 ▹
             I.Π xp₃ , xq₃ ▷ I.var x1 ▹
             I.Π I.𝟘 , xq₄ ▷ I.Id (I.var x2) (I.var x1) (I.var x0) ▹
             I.Id (I.Erased s (IW.wk[ 4 ] xl) (I.var x3))
               (I.box s (IW.wk[ 4 ] xl) (I.var x2))
               (I.box s (IW.wk[ 4 ] xl) (I.var x1)))
        (I.var! x2)        → I.base , I.term A (I.U xl)
        (I.var! x3)        → I.base , I.term t xA
        (I.var not-x4 _ _)

      []-cong″ᵢ : I.Termˢ 0 → I.Term c n₂
      []-cong″ᵢ s =
        I.lam xp₁′ (just (xq₁′ , I.U xl)) $
        I.lam xp₂′ (just (xq₂′ , I.var x0)) $
        I.lam xp₃′ (just (xq₃′ , I.var x1)) $
        I.lam I.𝟘
          (just (xq₄′ , I.Id (I.var x2) (I.var x1) (I.var x0))) $
        congᵢ I.𝟘
          (I.Erased s (IW.wk[ 4 ] xl)
             (I.Erased s (IW.wk[ 4 ] xl) (I.var x3)))
          (I.box s (IW.wk[ 4 ] xl) (I.box s (IW.wk[ 4 ] xl) (I.var x2)))
          (I.box s (IW.wk[ 4 ] xl) (I.box s (IW.wk[ 4 ] xl) (I.var x1)))
          (I.Erased s (IW.wk[ 4 ] xl) (I.var x3))
          (mapᴱᵢ (IW.wk[ 5 ] xl) (I.Erased s (IW.wk[ 5 ] xl) (I.var x4))
             (erasedᵢ (I.var x5) (I.var x0)) (I.var x0))
          (IW.wk[ 4 ] x[]-cong I.∘⟨ xp₁ ⟩
           I.Erased s (IW.wk[ 4 ] xl) (I.var x3) I.∘⟨ xp₂ ⟩
           I.box s (IW.wk[ 4 ] xl) (I.var x2) I.∘⟨ xp₃ ⟩
           I.box s (IW.wk[ 4 ] xl) (I.var x1) I.∘⟨ I.𝟘 ⟩
           congᵢ I.𝟘 (I.var x3) (I.var x2) (I.var x1)
             (I.Erased s (IW.wk[ 4 ] xl) (I.var x3))
             (I.box s (IW.wk[ 5 ] xl) (I.var x0))
             (I.var x0))

      opaque
        unfolding Erased [_]

        γ-wf :
          I.⟦ sᵢ ⟧ˢ (γ′ sᵢ) PE.≡ s →
          IC.Contexts-wf (I.base nothing) (γ′ sᵢ)
        γ-wf eq = λ where
          .IC.constraints-wf →
            let Unit-ok , Σ-ok = PE.subst Erased-allowed (PE.sym eq)
                                   Erased-ok
                _ , ⊢Π , ok₁   = inversion-ΠΣ $ wf-⊢ ⊢[]-cong′
                _ , ⊢Π , ok₂   = inversion-ΠΣ ⊢Π
                _ , ⊢Π , ok₃   = inversion-ΠΣ ⊢Π
                _ , _  , ok₄   = inversion-ΠΣ ⊢Π
            in
            Unit-ok  L.∷
            Σ-ok     L.∷
            hyp₁ ok₁ L.∷
            hyp₂ ok₂ L.∷
            hyp₃ ok₃ L.∷
            hyp₄ ok₄ L.∷
            L.[]
          .IC.metas-wf .IC.equalities-wf → L.[]
          .IC.metas-wf .IC.bindings-wf   → λ where
            (I.var! x0) → ⊢l
            (I.var! x1) →
              PE.subst (_⊢_∷_ _ _)
                (PE.cong (Π p₁ , q₁ ▷_▹_ _) $
                 PE.cong (Π p₂ , q₂ ▷_▹_ _) $
                 PE.cong (Π p₃ , q₃ ▷_▹_ _) $
                 PE.cong (Π 𝟘  , q₄ ▷_▹_ _) $
                 PE.cong
                   (λ s →
                      Id (Σ⟨ s ⟩ 𝟘 , 𝟘 ▷ var x3 ▹ Lift _ (Unit s))
                        (prod s 𝟘 (var x2) (lift (star s)))
                        (prod s 𝟘 (var x1) (lift (star s))))
                   (PE.sym eq)) $
              ⊢[]-cong′
            (I.var! x2)         → ⊢A
            (I.var! x3)         → ⊢t
            (I.var  not-x4 _ _)

    opaque

      ⊢l : ε » Γ ⊢ l ∷Level
      ⊢l = Has-[]-cong-for-level→⊢∷L has-[]-cong

    open Box-cong-internal (ε » Γ) l []-cong′ (Lift l ℕ) (lift zero)
           ⊢l ⊢[]-cong′
           (conv (Liftⱼ′ ⊢l (ℕⱼ (wf ⊢l)))
              (U-cong-⊢≡ (supᵘₗ-zeroˡ ⊢l)))
           (liftⱼ′ ⊢l (zeroⱼ (wf ⊢l)))

    private

      Goalᵢ : I.Termˢ 0 → I.Term c n
      Goalᵢ s =
        I.Π xp₁′ , xq₁′ ▷ I.U xl ▹
        I.Π xp₂′ , xq₂′ ▷ I.var x0 ▹
        I.Π xp₃′ , xq₃′ ▷ I.var x1 ▹
        I.Π I.𝟘  , xq₄′ ▷ I.Id (I.var x2) (I.var x1) (I.var x0) ▹
        I.Id (I.Erased s (IW.wk[ 4 ] xl) (I.var x3))
          (I.box s (IW.wk[ 4 ] xl) (I.var x2))
          (I.box s (IW.wk[ 4 ] xl) (I.var x1))

    opaque
      unfolding Erased cong erased fst⟨_⟩ mapᴱ subst [_]

      ⊢[]-cong″ :
        ε » Γ ⊢ []-cong″ ∷
        Π p₁′ , q₁′ ▷ U l ▹
        Π p₂′ , q₂′ ▷ var x0 ▹
        Π p₃′ , q₃′ ▷ var x1 ▹
        Π 𝟘   , q₄′ ▷ Id (var x2) (var x1) (var x0) ▹
        Id (Erased (wk[ 4 ]′ l) (var x3)) [ var x2 ] ([ var x1 ])
      ⊢[]-cong″ = case PE.singleton s of λ where
        (𝕤 , PE.refl) →
          check-type-and-term-sound (γ′ I.𝕤) (I.base nothing I.» I.base)
            ([]-cong″ᵢ I.𝕤) (Goalᵢ I.𝕤) 22 PE.refl (γ-wf PE.refl)
            (wf ⊢l)
        (𝕨 , PE.refl) →
          check-type-and-term-sound (γ′ I.𝕨) (I.base nothing I.» I.base)
            ([]-cong″ᵢ I.𝕨) (Goalᵢ I.𝕨) 21 PE.refl (γ-wf PE.refl)
            (wf ⊢l)

opaque

  -- One can replace some of the "p" grades in Has-[]-cong-for-level
  -- with grades that satisfy certain assumptions (given certain
  -- assumptions).
  --
  -- Note that, if all Π-types are allowed and l is a level literal,
  -- then all of the assumptions are satisfied for the erasure
  -- modality with 𝟘ᵐ.

  Has-[]-cong-for-level-stronger :
    {Γ : Con Term n} →
    (s PE.≡ 𝕨 → ¬ T 𝟘ᵐ-allowed → Trivial) →
    (s PE.≡ 𝕨 → Prodrec-allowed 𝟘ᵐ? (𝟘 ∧ 𝟙) 𝟘 𝟘) →
    (s PE.≡ 𝕤 → ¬ T 𝟘ᵐ-allowed → 𝟘 ≤ 𝟙) →
    (Π-allowed p₁ q₁ → Π-allowed p₁′ q₁′) →
    (Π-allowed p₂ q₂ → Π-allowed p₂′ q₂′) →
    (Π-allowed p₃ q₃ → Π-allowed p₃′ q₃′) →
    (Π-allowed 𝟘  q₄ → Π-allowed 𝟘   q₄′) →
    ⌜ m ⌝ · p₁′ ≤ 𝟘 →
    ⌜ m ⌝ · p₂′ ≤ 𝟘 →
    ⌜ m ⌝ · p₃′ ≤ 𝟘 →
    γ ▸[ 𝟘ᵐ? ] l →
    Has-[]-cong-for-level s m Γ l p₁ q₁ p₂ q₂ p₃ q₃ q₄ →
    Has-[]-cong-for-level s m Γ l p₁′ q₁′ p₂′ q₂′ p₃′ q₃′ q₄′
  Has-[]-cong-for-level-stronger
    {s} {p₁} {p₁′} {p₂} {p₂′} {p₃} {p₃′} {m}
    trivial P-ok 𝟘≤𝟙 hyp₁ hyp₂ hyp₃ hyp₄ hyp₁′ hyp₂′ hyp₃′ ▸l
    has-[]-cong@(_ , ▸[]-cong′ , _) =
    []-cong″ , ▸[]-cong″ , ⊢[]-cong″
    where
    open ErasedU s using (▸Erased; ▸[])
    open ErasedU₀₁ s
    open Has-[]-cong-for-level-stronger hyp₁ hyp₂ hyp₃ hyp₄ has-[]-cong

    ▸[]-cong″ : 𝟘ᶜ ▸[ m ] []-cong″
    ▸[]-cong″ =
      let ▸l′ = wkUsage _ ▸l in
      lamₘ $ lamₘ $ lamₘ $ lamₘ $
      sub
        (▸cong (▸Erased ▸l′ (▸Erased ▸l′ var)) (▸[] (▸[] var))
           (▸[] (▸[] var)) (▸Erased ▸l′ var)
           (sub
              (▸mapᴱ′ trivial P-ok 𝟘≤𝟙
                 (λ _ → _ , ▸Erased (wkUsage _ ▸l) var)
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
              (▸cong var var var (▸Erased ▸l′ var)
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
            flip _∘ₘ_ (▸Erased ▸l′ var) $
            wkUsage _ ▸[]-cong′)
           (λ _ → begin
              𝟘ᶜ ∙ ⌜ m ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
              𝟘ᶜ              ∎)
           (λ _ → begin
              𝟘ᶜ                                        ≈˘⟨ ≈ᶜ-trans (+ᶜ-cong (·ᶜ-zeroʳ _) (≈ᶜ-trans (+ᶜ-identityˡ _) (·ᶜ-zeroʳ _))) $
                                                            +ᶜ-identityʳ _ ⟩
              (⌜ m ⌝ · 𝟘) ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ (𝟙 + 𝟙) ·ᶜ 𝟘ᶜ  ∎)) $
      (begin
         𝟘ᶜ ∙ ⌜ m ⌝ · p₁′ ∙ ⌜ m ⌝ · p₂′ ∙ ⌜ m ⌝ · p₃′ ∙ ⌜ m ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩

         𝟘ᶜ ∙ ⌜ m ⌝ · p₁′ ∙ ⌜ m ⌝ · p₂′ ∙ ⌜ m ⌝ · p₃′ ∙ 𝟘          ≤⟨ ≤ᶜ-refl ∙ hyp₁′ ∙ hyp₂′ ∙ hyp₃′ ∙ ≤-refl ⟩

         𝟘ᶜ                                                        ≈˘⟨ ≈ᶜ-trans
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
                                                                                              (+ᶜ-identityˡ _) $
                                                                                            ·ᶜ-zeroʳ _)
                                                                                           (·ᶜ-zeroʳ _)) $
                                                                                      +ᶜ-identityʳ _)
                                                                                     (·ᶜ-zeroʳ _)) $
                                                                                +ᶜ-identityʳ _)
                                                                               (·ᶜ-zeroˡ _)) $
                                                                          +ᶜ-identityʳ _) $
                                                                       ·ᶜ-zeroʳ _ ⟩
         ω ·ᶜ
         (𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ
          ((((𝟘ᶜ +ᶜ p₁ ·ᶜ 𝟘ᶜ) +ᶜ p₂ ·ᶜ 𝟘ᶜ) +ᶜ p₃ ·ᶜ 𝟘ᶜ) +ᶜ
           𝟘 ·ᶜ ω ·ᶜ
           ((𝟘ᶜ , x2 ≔ ⌜ m ᵐ· 𝟘 ⌝) +ᶜ (𝟘ᶜ , x1 ≔ ⌜ m ᵐ· 𝟘 ⌝) +ᶜ
            (𝟘ᶜ , x0 ≔ ⌜ m ᵐ· 𝟘 ⌝) +ᶜ 𝟘ᶜ)) +ᶜ
          𝟘ᶜ)                                                      ∎)
      where
      open ≤ᶜ-reasoning

opaque
  unfolding Has-[]-cong-for-level-stronger

  -- One can replace some of the "p" grades in
  -- Has-computing-[]-cong-for-level with grades that satisfy certain
  -- assumptions (given certain assumptions).
  --
  -- Note that, if all Π-types are allowed and l is a level literal,
  -- then all the assumptions are satisfied for the erasure modality
  -- with 𝟘ᵐ.

  Has-computing-[]-cong-for-level-stronger :
    {Γ : Con Term n} →
    (s PE.≡ 𝕨 → ¬ T 𝟘ᵐ-allowed → Trivial) →
    (s PE.≡ 𝕨 → Prodrec-allowed 𝟘ᵐ? (𝟘 ∧ 𝟙) 𝟘 𝟘) →
    (s PE.≡ 𝕤 → ¬ T 𝟘ᵐ-allowed → 𝟘 ≤ 𝟙) →
    (Π-allowed p₁ q₁ → Π-allowed p₁′ q₁′) →
    (Π-allowed p₂ q₂ → Π-allowed p₂′ q₂′) →
    (Π-allowed p₃ q₃ → Π-allowed p₃′ q₃′) →
    (Π-allowed 𝟘  q₄ → Π-allowed 𝟘   q₄′) →
    ⌜ m ⌝ · p₁′ ≤ 𝟘 →
    ⌜ m ⌝ · p₂′ ≤ 𝟘 →
    ⌜ m ⌝ · p₃′ ≤ 𝟘 →
    γ ▸[ 𝟘ᵐ? ] l →
    Has-computing-[]-cong-for-level s m Γ l p₁ q₁ p₂ q₂ p₃ q₃ q₄ →
    Has-computing-[]-cong-for-level s m Γ l p₁′ q₁′ p₂′ q₂′ p₃′ q₃′ q₄′
  Has-computing-[]-cong-for-level-stronger
    {n} {s} {p₁} {q₁} {p₁′} {q₁′} {p₂} {q₂} {p₂′} {q₂′} {p₃} {q₃}
    {p₃′} {q₃′} {q₄} {q₄′} {m} {l} {Γ}
    trivial P-ok 𝟘≤𝟙 hyp₁ hyp₂ hyp₃ hyp₄ hyp₁′ hyp₂′ hyp₃′ ▸l
    (has-[]-cong@([]-cong′ , _ , ⊢[]-cong′) , []-cong′≡) =
    has-[]-cong′ , []-cong″-computes
    where
    open Erased s
    open Erased.Internal s Zero-one-isMode TR
    open Has-[]-cong-for-level-stronger
           hyp₁ hyp₂ hyp₃ hyp₄ has-[]-cong

    has-[]-cong′ :
      Has-[]-cong-for-level s m Γ l p₁′ q₁′ p₂′ q₂′ p₃′ q₃′ q₄′
    has-[]-cong′ =
      Has-[]-cong-for-level-stronger
        trivial P-ok 𝟘≤𝟙 hyp₁ hyp₂ hyp₃ hyp₄ hyp₁′ hyp₂′ hyp₃′ ▸l has-[]-cong

    opaque

      []-cong″-computes :
        ∀ m n′ (Δ : Cons m n′) (A t : Term n′) (ρ : Wk n′ n) →
        Δ .defs » ρ ∷ʷ Δ .vars ⊇ Γ →
        Δ ⊢ A ∷ U (wk ρ l) →
        Δ ⊢ t ∷ A →
        Δ ⊢
          wk ρ []-cong″ ∘⟨ p₁′ ⟩ A ∘⟨ p₂′ ⟩ t ∘⟨ p₃′ ⟩ t ∘⟨ 𝟘 ⟩ rfl ≡
          rfl ∷ Id (Erased (wk ρ l) A) [ t ] ([ t ])
      []-cong″-computes m n′ Δ A t ρ Δ⊇Γ ⊢A ⊢t =
        wk ρ
          (lam p₁′ $ lam p₂′ $ lam p₃′ $ lam 𝟘 $
           cong 𝟘 (Erased (wk[ 4 ]′ l) (Erased (wk[ 4 ]′ l) (var x3)))
             [ [ var x2 ] ] [ [ var x1 ] ]
             (Erased (wk[ 4 ]′ l) (var x3))
             (mapᴱ (Erased (wk[ 5 ]′ l) (var x4))
                (erased (var x5) (var x0)) (var x0))
             (wk[ 4 ]′ []-cong′ ∘⟨ p₁ ⟩ Erased (wk[ 4 ]′ l) (var x3)
                ∘⟨ p₂ ⟩ [ var x2 ] ∘⟨ p₃ ⟩ [ var x1 ]
                ∘⟨ 𝟘 ⟩ cong 𝟘 (var x3) (var x2) (var x1)
                         (Erased (wk[ 4 ]′ l) (var x3)) [ var x0 ]
                         (var x0)))
          ∘⟨ p₁′ ⟩ A ∘⟨ p₂′ ⟩ t ∘⟨ p₃′ ⟩ t ∘⟨ 𝟘 ⟩ rfl                     ≡⟨ PE.cong (flip _∘⟨ 𝟘   ⟩_ _) $
                                                                             PE.cong (flip _∘⟨ p₃′ ⟩_ _) $
                                                                             PE.cong (flip _∘⟨ p₂′ ⟩_ _) $
                                                                             PE.cong (flip _∘⟨ p₁′ ⟩_ _) $
                                                                             PE.cong (lam _ ∘→ lam _ ∘→ lam _ ∘→ lam _) $
                                                                             PE.trans wk-cong $
                                                                             PE.cong₆ (cong _)
                                                                               (PE.trans wk-Erased $
                                                                                PE.cong₂ Erased (wk⇑[]-wk[]≡ 4) $
                                                                                PE.trans wk-Erased $
                                                                                PE.cong (flip Erased _) (wk⇑[]-wk[]≡ 4))
                                                                               (PE.trans wk-[] $
                                                                                PE.cong [_] wk-[])
                                                                               (PE.trans wk-[] $
                                                                                PE.cong [_] wk-[])
                                                                               (PE.trans wk-Erased $
                                                                                PE.cong (flip Erased _) (wk⇑[]-wk[]≡ 4))
                                                                               (PE.trans wk-mapᴱ $
                                                                                PE.cong₃ mapᴱ
                                                                                  (PE.trans wk-Erased $
                                                                                   PE.cong (flip Erased _) (wk⇑[]-wk[]≡ 5))
                                                                                  wk-erased PE.refl)
                                                                               (PE.cong₂ _∘⟨ 𝟘 ⟩_
                                                                                  (PE.cong₂ _∘⟨ p₃ ⟩_
                                                                                     (PE.cong₂ _∘⟨ p₂ ⟩_
                                                                                        (PE.cong₂ _∘⟨ p₁ ⟩_
                                                                                           (wk⇑[]-wk[]≡ 4)
                                                                                           (PE.trans wk-Erased $
                                                                                            PE.cong (flip Erased _) (wk⇑[]-wk[]≡ 4)))
                                                                                        wk-[])
                                                                                     wk-[]) $
                                                                                PE.trans wk-cong $
                                                                                PE.cong₃ (cong _ _ _ _)
                                                                                  (PE.trans wk-Erased $
                                                                                   PE.cong (flip Erased _) (wk⇑[]-wk[]≡ 4))
                                                                                  wk-[]
                                                                                  PE.refl) ⟩⊢≡
        (lam p₁′ $ lam p₂′ $ lam p₃′ $ lam 𝟘 $
         cong 𝟘
           (Erased (wk[ 4 ]′ (wk ρ l))
              (Erased (wk[ 4 ]′ (wk ρ l)) (var x3)))
           [ [ var x2 ] ] [ [ var x1 ] ]
           (Erased (wk[ 4 ]′ (wk ρ l)) (var x3))
           (mapᴱ (Erased (wk[ 5 ]′ (wk ρ l)) (var x4))
              (erased (var x5) (var x0)) (var x0))
           (wk[ 4 ]′ (wk ρ []-cong′)
              ∘⟨ p₁ ⟩ Erased (wk[ 4 ]′ (wk ρ l)) (var x3)
              ∘⟨ p₂ ⟩ [ var x2 ] ∘⟨ p₃ ⟩ [ var x1 ]
              ∘⟨ 𝟘 ⟩ cong 𝟘 (var x3) (var x2) (var x1)
                       (Erased (wk[ 4 ]′ (wk ρ l)) (var x3))
                       [ var x0 ] (var x0)))
          ∘⟨ p₁′ ⟩ A ∘⟨ p₂′ ⟩ t ∘⟨ p₃′ ⟩ t ∘⟨ 𝟘 ⟩ rfl ∷
          Id (Erased (wk ρ l) A) [ t ] ([ t ])                            ≡⟨ lemma₁ ⟩⊢∷
                                                                           ⟨ lemma₂ ⟩≡
        cong 𝟘 (Erased (wk ρ l) (Erased (wk ρ l) A)) [ [ t ] ] [ [ t ] ]
          (Erased (wk ρ l) A)
          (mapᴱ (Erased (wk1 (wk ρ l)) (wk1 A))
             (erased (wk₂ A) (var x0)) (var x0))
          (wk ρ []-cong′ ∘⟨ p₁ ⟩ Erased (wk ρ l) A ∘⟨ p₂ ⟩ [ t ]
             ∘⟨ p₃ ⟩ [ t ] ∘⟨ 𝟘 ⟩ rfl) ∷
          Id (Erased (wk ρ l) A)
            (mapᴱ (Erased (wk1 (wk ρ l)) (wk1 A))
               (erased (wk₂ A) (var x0)) (var x0) [ [ [ t ] ] ]₀)
            (mapᴱ (Erased (wk1 (wk ρ l)) (wk1 A))
               (erased (wk₂ A) (var x0)) (var x0) [ [ [ t ] ] ]₀)         ≡⟨ cong-cong (refl ⊢Erased-Erased-A) (refl ⊢[[t]]) (refl ⊢[[t]])
                                                                               (refl (univ ⊢Erased-A)) (refl ⊢mapᴱ-0) $
                                                                             []-cong′≡ _ _ _ _ _ _ Δ⊇Γ ⊢Erased-A ⊢[t] ⟩⊢∷
        cong 𝟘 (Erased (wk ρ l) (Erased (wk ρ l) A)) [ [ t ] ] [ [ t ] ]
          (Erased (wk ρ l) A)
          (mapᴱ (Erased (wk1 (wk ρ l)) (wk1 A))
             (erased (wk₂ A) (var x0)) (var x0))
          rfl                                                             ⇒⟨ cong-⇒ ⊢[[t]] ⊢mapᴱ-0 ⟩⊢∎

        rfl                                                               ∎
        where
        opaque

          Δ⊇ε : WD.» Δ .defs ⊇ ε
          Δ⊇ε = WD.»⊇ε (defn-wf (wf ⊢A))

        opaque

          ⊢wk-l : Δ ⊢ wk ρ l ∷Level
          ⊢wk-l = W.wk Δ⊇Γ (WD.defn-wk Δ⊇ε ⊢l)

        open Box-cong-internal Δ (wk ρ l) (wk ρ []-cong′) A t
               ⊢wk-l
               (PE.subst (_⊢_∷_ _ _)
                  (PE.cong (Π p₁ , q₁ ▷_▹_ _) $
                   PE.cong (Π p₂ , q₂ ▷_▹_ _) $
                   PE.cong (Π p₃ , q₃ ▷_▹_ _) $
                   PE.cong (Π 𝟘  , q₄ ▷_▹_ _) $
                   PE.cong₃ Id
                     (PE.trans wk-Erased $
                      PE.cong (flip Erased _) (wk⇑[]-wk[]≡ 4))
                     wk-[] wk-[]) $
                W.wk Δ⊇Γ (WD.defn-wk Δ⊇ε ⊢[]-cong′))
               ⊢A ⊢t

        opaque

          ⊢Erased-A : Δ ⊢ Erased (wk ρ l) A ∷ U (wk ρ l)
          ⊢Erased-A = Erasedⱼ-U Erased-ok ⊢A

        opaque

          ⊢Erased-Erased-A : Δ ⊢ Erased (wk ρ l) (Erased (wk ρ l) A)
          ⊢Erased-Erased-A = Erasedⱼ Erased-ok ⊢wk-l (univ ⊢Erased-A)

        opaque

          ⊢[t] : Δ ⊢ [ t ] ∷ Erased (wk ρ l) A
          ⊢[t] = []ⱼ Erased-ok ⊢wk-l ⊢t

        opaque

          ⊢[[t]] : Δ ⊢ [ [ t ] ] ∷ Erased (wk ρ l) (Erased (wk ρ l) A)
          ⊢[[t]] = []ⱼ Erased-ok ⊢wk-l ⊢[t]

        opaque

          ⊢mapᴱ-0 :
            Δ »∙ Erased (wk ρ l) (Erased (wk ρ l) A) ⊢
            mapᴱ (Erased (wk1 (wk ρ l)) (wk1 A))
              (erased (wk₂ A) (var x0)) (var x0) ∷
            wk1 (Erased (wk ρ l) A)
          ⊢mapᴱ-0 =
            PE.subst (_⊢_∷_ _ _) (PE.sym wk-Erased) $
            ⊢mapᴱ (W.wk₁ ⊢Erased-Erased-A ⊢wk-l)
              (PE.subst (flip (_⊢_∷_ _) _)
                 (PE.cong (flip erased _) wk[]≡wk[]′) $
               erasedⱼ $ PE.subst (_⊢_∷_ _ _) wk-Erased $
               var₀ $ PE.subst (_⊢_ _) wk-Erased $
               W.wk₁ ⊢Erased-Erased-A (univ ⊢Erased-A))
              (PE.subst (_⊢_∷_ _ _)
                 (PE.trans wk-Erased $ PE.cong (Erased _) wk-Erased) $
               var₀ ⊢Erased-Erased-A)

        lhsᵢ : I.Termˢ 0 → I.Term c n′
        lhsᵢ s =
          []-cong″ᵢ s I.∘⟨ xp₁′ ⟩ xA I.∘⟨ xp₂′ ⟩ xt I.∘⟨ xp₃′ ⟩ xt
            I.∘⟨ I.𝟘 ⟩ I.rfl nothing

        rhsᵢ : I.Termˢ 0 → I.Term c n′
        rhsᵢ s =
          congᵢ I.𝟘 (I.Erased s xl (I.Erased s xl xA))
            (I.box s xl (I.box s xl xt)) (I.box s xl (I.box s xl xt))
            (I.Erased s xl xA)
            (mapᴱᵢ (IW.wk[ 1 ] xl)
               (I.Erased s (IW.wk[ 1 ] xl) (IW.wk[ 1 ] xA))
               (erasedᵢ (IW.wk[ 2 ] xA) (I.var x0)) (I.var x0))
            (x[]-cong I.∘⟨ xp₁ ⟩ I.Erased s xl xA
               I.∘⟨ xp₂ ⟩ I.box s xl xt I.∘⟨ xp₃ ⟩ I.box s xl xt
               I.∘⟨ I.𝟘 ⟩ I.rfl nothing)

        Lhsᵢ : I.Termˢ 0 → I.Term c n′
        Lhsᵢ s =
          I.Id (I.Erased s xl xA) (I.box s xl xt) (I.box s xl xt)

        Rhsᵢ : I.Termˢ 0 → I.Term c n′
        Rhsᵢ s =
          let tm =
                I.subst
                  (mapᴱᵢ (IW.wk[ 1 ] xl)
                     (I.Erased s (IW.wk[ 1 ] xl) (IW.wk[ 1 ] xA))
                     (erasedᵢ (IW.wk[ 2 ] xA) (I.var x0)) (I.var x0))
                  (IS.sgSubst (I.box s xl (I.box s xl xt)))
          in
          I.Id (I.Erased s xl xA) tm tm

        opaque
          unfolding Erased cong erased fst⟨_⟩ mapᴱ subst [_]

          lemma₁ :
            Δ ⊢
              (lam p₁′ $ lam p₂′ $ lam p₃′ $ lam 𝟘 $
               cong 𝟘
                 (Erased (wk[ 4 ]′ (wk ρ l))
                    (Erased (wk[ 4 ]′ (wk ρ l)) (var x3)))
                 [ [ var x2 ] ] [ [ var x1 ] ]
                 (Erased (wk[ 4 ]′ (wk ρ l)) (var x3))
                 (mapᴱ (Erased (wk[ 5 ]′ (wk ρ l)) (var x4))
                    (erased (var x5) (var x0)) (var x0))
                 (wk[ 4 ]′ (wk ρ []-cong′)
                    ∘⟨ p₁ ⟩ Erased (wk[ 4 ]′ (wk ρ l)) (var x3)
                    ∘⟨ p₂ ⟩ [ var x2 ] ∘⟨ p₃ ⟩ [ var x1 ]
                    ∘⟨ 𝟘 ⟩ cong 𝟘 (var x3) (var x2) (var x1)
                             (Erased (wk[ 4 ]′ (wk ρ l)) (var x3))
                             [ var x0 ] (var x0)))
                ∘⟨ p₁′ ⟩ A ∘⟨ p₂′ ⟩ t ∘⟨ p₃′ ⟩ t ∘⟨ 𝟘 ⟩ rfl ≡
              cong 𝟘 (Erased (wk ρ l) (Erased (wk ρ l) A)) [ [ t ] ]
                [ [ t ] ] (Erased (wk ρ l) A)
                (mapᴱ (Erased (wk1 (wk ρ l)) (wk1 A))
                   (erased (wk₂ A) (var x0)) (var x0))
                (wk ρ []-cong′ ∘⟨ p₁ ⟩ Erased (wk ρ l) A ∘⟨ p₂ ⟩ [ t ]
                   ∘⟨ p₃ ⟩ [ t ] ∘⟨ 𝟘 ⟩ rfl) ∷
              Id (Erased (wk ρ l) A) [ t ] ([ t ])
          lemma₁ = case PE.singleton s of λ where
            (𝕤 , PE.refl) →
              check-and-equal-type-and-terms-sound (γ′ I.𝕤)
                (I.base nothing I.» I.base) (lhsᵢ I.𝕤) (rhsᵢ I.𝕤)
                (Lhsᵢ I.𝕤) 29 PE.refl (γ-wf PE.refl) (wf ⊢A)
            (𝕨 , PE.refl) →
              check-and-equal-type-and-terms-sound (γ′ I.𝕨)
                (I.base nothing I.» I.base) (lhsᵢ I.𝕨) (rhsᵢ I.𝕨)
                (Lhsᵢ I.𝕨) 28 PE.refl (γ-wf PE.refl) (wf ⊢A)

        opaque
          unfolding Erased erased fst⟨_⟩ mapᴱ [_]

          lemma₂ :
            Δ ⊢ Id (Erased (wk ρ l) A) [ t ] ([ t ]) ≡
              Id (Erased (wk ρ l) A)
                (mapᴱ (Erased (wk1 (wk ρ l)) (wk1 A))
                   (erased (wk₂ A) (var x0)) (var x0) [ [ [ t ] ] ]₀)
                (mapᴱ (Erased (wk1 (wk ρ l)) (wk1 A))
                   (erased (wk₂ A) (var x0)) (var x0) [ [ [ t ] ] ]₀)
          lemma₂ = case PE.singleton s of λ where
            (𝕤 , PE.refl) →
              check-and-equal-ty-sound (γ′ I.𝕤)
                (I.base nothing I.» I.base) (Lhsᵢ I.𝕤) (Rhsᵢ I.𝕤) 15
                PE.refl (γ-wf PE.refl) (wf ⊢A)
            (𝕨 , PE.refl) →
              check-and-equal-ty-sound (γ′ I.𝕨)
                (I.base nothing I.» I.base) (Lhsᵢ I.𝕨) (Rhsᵢ I.𝕨) 14
                PE.refl (γ-wf PE.refl) (wf ⊢A)
