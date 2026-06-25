------------------------------------------------------------------------
-- Sometimes []-cong can be defined, sometimes it cannot be defined
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
import Graded.Modality
import Graded.Mode.Instances.Zero-one
open import Graded.Mode.Instances.Zero-one.Variant
open import Graded.Usage.Restrictions

module Graded.Has-box-cong.Definable
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

open import Definition.Conversion.Consequences.Var TR
open import Definition.Typed TR
open import Definition.Typed.Consequences.Admissible Zero-one-isMode TR
open import Definition.Typed.Consequences.Consistency TR
open import Definition.Typed.Consequences.Inversion TR
open import Definition.Typed.Consequences.Reduction TR
open import Definition.Typed.EqRelInstance TR
open import Definition.Typed.Inversion TR
open import Definition.Typed.Properties TR hiding ([]-cong′)
open import Definition.Typed.Reasoning.Term TR
open import Definition.Typed.Substitution TR
import Definition.Typed.Weakening TR as W
import Definition.Typed.Weakening.Definition TR as WD
open import Definition.Typed.Well-formed TR
open import Definition.Untyped M
import Definition.Untyped.Erased 𝕄 as Erased
open import Definition.Untyped.Inversion M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M
open import Definition.Untyped.Whnf M type-variant

open import Graded.Has-box-cong TR UR
open import Graded.Has-box-cong.Definable.J TR UR
open import Graded.Has-box-cong.Equivalent TR UR
open import Graded.Has-box-cong.Equivalent.For-level TR UR
open import Graded.Has-box-cong.Lemmas TR variant
open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Modality.Properties 𝕄
open import Graded.Neutral TR UR
open import Graded.Reduction.Zero-one variant TR UR
open import Graded.Restrictions.Zero-one 𝕄 variant
open import Graded.Usage UR
open import Graded.Usage.Erased-matches
open import Graded.Usage.Properties UR
open import Graded.Usage.Weakening UR

open import Tools.Bool using (T)
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+; 2+; 3+)
open import Tools.Product as Σ
open import Tools.PropositionalEquality as PE using (_≢_)
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum using (_⊎_; inj₁; inj₂)

private variable
  n n′                                     : Nat
  Δ                                        : Con Term _
  Γ                                        : Cons _ _
  A B C t u v                              : Term _
  l                                        : Lvl _
  σ                                        : Subst _ _
  p p₁ p₂ p₃ p₄ q₁ q₂ q₂′ q₃ q₃′ q₄ q₄′ q₅ : M
  γ γ₁ γ₂ γ₃ γ₄ γ₅                         : Conₘ _
  m                                        : Mode
  s                                        : Strength

------------------------------------------------------------------------
-- []-cong can sometimes be defined

-- Some definitions used in
-- []-cong⊎J⊎𝟘ᵐ⊎Trivial⊎Equality-reflection→[]-cong-for-level and
-- []-cong⊎J⊎𝟘ᵐ⊎Trivial⊎Equality-reflection→[]-cong.

private
  module []-cong⊎J⊎𝟘ᵐ⊎Trivial⊎Equality-reflection→[]-cong
    (ok : ([]-cong-allowed s × []-cong-allowed-mode s m) ⊎
          Erased-allowed s ×
          (erased-matches-for-J m ≢ none × T 𝟘ᵐ-allowed ⊎
           (∃ λ ok → m PE.≡ 𝟘ᵐ[ ok ]) ⊎
           Trivial ⊎
           Equality-reflection))
    (ok₂ : Π-allowed 𝟘 q₂)
    (ok₃ : Π-allowed 𝟘 q₃)
    (ok₄ : Π-allowed 𝟘 q₄)
    (ok₅ : Π-allowed 𝟘 q₅)
    where

    opaque

      Erased-ok : Erased-allowed s
      Erased-ok = case ok of λ where
        (inj₁ (ok , _)) → []-cong→Erased ok
        (inj₂ (ok , _)) → ok

    OK : Set a
    OK =
      ([]-cong-allowed s × []-cong-allowed-mode s m) ⊎
      Equality-reflection ⊎
      (∃ λ sem → erased-matches-for-J m PE.≡ not-none sem) ×
        T 𝟘ᵐ-allowed ⊎
      (∃ λ ok → m PE.≡ 𝟘ᵐ[ ok ]) ⊎
      Trivial

    opaque

      ok′ : OK
      ok′ = case ok of λ where
        (inj₁ ok) →
          inj₁ ok
        (inj₂ (_ , inj₂ (inj₂ (inj₂ ok)))) →
          inj₂ (inj₁ ok)
        (inj₂ (_ , inj₂ (inj₂ (inj₁ trivial)))) →
          inj₂ (inj₂ (inj₂ (inj₂ trivial)))
        (inj₂ (_ , inj₂ (inj₁ ok))) →
          inj₂ (inj₂ (inj₂ (inj₁ ok)))
        (inj₂ (_ , inj₁ (≢none , ok))) →
          inj₂ $ inj₂ $ inj₁ $
          case PE.singleton $ erased-matches-for-J m of λ where
            (not-none _ , ≡not-none) → (_ , ≡not-none) , ok
            (none       , ≡none)     → ⊥-elim $ ≢none ≡none

    []-cong′ :
      OK → Lvl n′ → Term n′ → Term n′ → Term n′ → Term n′ → Term n′
    []-cong′ (inj₁ _)        = []-cong s
    []-cong′ (inj₂ (inj₁ _)) = λ _ _ _ _ _ → rfl
    []-cong′ (inj₂ (inj₂ _)) = []-cong-J s

    opaque

      ▸[]-cong′ :
        ∀ ok →
        γ₁ ▸[ 𝟘ᵐ? ] l →
        γ₂ ▸[ 𝟘ᵐ? ] A →
        γ₃ ▸[ 𝟘ᵐ? ] t →
        γ₄ ▸[ 𝟘ᵐ? ] u →
        γ₅ ▸[ 𝟘ᵐ? ] v →
        𝟘ᶜ ▸[ m ] []-cong′ ok l A t u v
      ▸[]-cong′ (inj₁ (_ , ok)) ▸l ▸A ▸t ▸u ▸v =
        []-congₘ ▸l ▸A ▸t ▸u ▸v ok
      ▸[]-cong′ (inj₂ (inj₁ ok)) _ _ _ _ _ =
        rflₘ
      ▸[]-cong′
        (inj₂ (inj₂ (inj₁ ((_ , ≡not-none) , ok)))) ▸l ▸A ▸t ▸u ▸v =
        ▸[]-cong-J {ok = ok} ≡not-none (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸l)
          (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸A) (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸t) (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸u)
          (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸v)
      ▸[]-cong′
        (inj₂ (inj₂ (inj₂ (inj₁ (_ , PE.refl))))) ▸l ▸A ▸t ▸u ▸v =
        ▸[]-cong-J-𝟘ᵐ (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸l) (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸A)
          (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸t) (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸u) (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸v)
      ▸[]-cong′ (inj₂ (inj₂ (inj₂ (inj₂ trivial)))) =
        ▸[]-cong-J-trivial trivial

    opaque

      ⊢[]-cong′ :
        let open Erased s in
        ∀ ok →
        Γ ⊢ l ∷Level →
        Γ ⊢ v ∷ Id A t u →
        Γ ⊢ []-cong′ ok l A t u v ∷ Id (Erased l A) [ t ] ([ u ])
      ⊢[]-cong′ (inj₁ (ok , _))  = []-congⱼ′ ok
      ⊢[]-cong′ (inj₂ (inj₂ _))  = []-cong-Jⱼ Erased-ok
      ⊢[]-cong′ (inj₂ (inj₁ ok)) =
        []-cong-with-equality-reflection ok Erased-ok

    opaque

      ⊢[]-cong′-3-2-1-0 :
        let open Erased s in
        Γ ⊢ l ∷Level →
        Γ »∙ U l »∙ var x0 »∙ var x1 »∙ Id (var x2) (var x1) (var x0) ⊢
          []-cong′ ok′ (wk[ 4 ]′ l) (var x3) (var x2) (var x1)
            (var x0) ∷
          Id (Erased (wk[ 4 ]′ l) (var x3)) [ var x2 ] ([ var x1 ])
      ⊢[]-cong′-3-2-1-0 ⊢l =
        let ⊢Id = ⊢Id-2-1-0′ ⊢l in
        ⊢[]-cong′ ok′ (W.wk (W.ʷ⊇-drop (∙ ⊢Id)) ⊢l) (var₀ ⊢Id)

    opaque

      ⊢[]-cong′-4-3-2-1-0 :
        let open Erased s in
        Level-allowed →
        ⊢ Γ →
        Γ »∙ Level »∙ U (level (var x0)) »∙ var x0 »∙ var x1 »∙
          Id (var x2) (var x1) (var x0) ⊢
          []-cong′ ok′ (level (var x4)) (var x3) (var x2) (var x1)
            (var x0) ∷
          Id (Erased (level (var x4)) (var x3)) [ var x2 ] ([ var x1 ])
      ⊢[]-cong′-4-3-2-1-0 Level-ok ⊢Γ =
        ⊢[]-cong′-3-2-1-0 (term-⊢∷ (var₀ (Levelⱼ′ Level-ok ⊢Γ)))

    opaque

      []-cong′-[] :
        ∀ ok →
        []-cong′ ok l A t u v [ σ ] PE.≡
        []-cong′ ok (l [ σ ]) (A [ σ ]) (t [ σ ]) (u [ σ ]) (v [ σ ])
      []-cong′-[] (inj₁ _)         = PE.refl
      []-cong′-[] (inj₂ (inj₁ ok)) = PE.refl
      []-cong′-[] (inj₂ (inj₂ _))  = []-cong-J-[]

    opaque

      []-cong′-β-⇒* :
        let open Erased s in
        ∀ ok →
        Γ ⊢ l ∷Level →
        Γ ⊢ t ∷ A →
        Γ ⊢ []-cong′ ok l A t t rfl ⇒* rfl ∷
          Id (Erased l A) [ t ] ([ t ])
      []-cong′-β-⇒* (inj₁ (ok , _)) ⊢l ⊢t =
        redMany ([]-cong-β ⊢l (refl ⊢t) ok)
      []-cong′-β-⇒* (inj₂ (inj₂ _)) ⊢l ⊢t =
        redMany ([]-cong-J-β-⇒ Erased-ok ⊢l ⊢t)
      []-cong′-β-⇒* (inj₂ (inj₁ ok)) ⊢l ⊢t =
        id ([]-cong-with-equality-reflection ok Erased-ok ⊢l (rflⱼ ⊢t))

    []-cong₁ : Lvl n → Term n
    []-cong₁ l =
      lam 𝟘 $ lam 𝟘 $ lam 𝟘 $ lam 𝟘 $
      []-cong′ ok′ (wk[ 4 ]′ l) (var x3) (var x2) (var x1) (var x0)

    opaque

      ▸[]-cong₁ : γ ▸[ 𝟘ᵐ? ] l → 𝟘ᶜ ▸[ m ] []-cong₁ l
      ▸[]-cong₁ ▸l =
        lamₘ $ lamₘ $ lamₘ $ lamₘ $
        sub (▸[]-cong′ ok′ (wkUsage _ ▸l) var var var var) $ begin
          𝟘ᶜ ∙ ⌜ m ⌝ · 𝟘 ∙ ⌜ m ⌝ · 𝟘 ∙ ⌜ m ⌝ · 𝟘 ∙ ⌜ m ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ⟩

          𝟘ᶜ                                                  ∎
        where
        open Tools.Reasoning.PartialOrder ≤ᶜ-poset

    opaque

      ⊢[]-cong₁ :
        let open Erased s in
        Γ ⊢ l ∷Level →
        Γ ⊢ []-cong₁ l ∷
        Π 𝟘 , q₂ ▷ U l ▹
        Π 𝟘 , q₃ ▷ var x0 ▹
        Π 𝟘 , q₄ ▷ var (x0 +1) ▹
        Π 𝟘 , q₅ ▷ Id (var ((x0 +1) +1)) (var (x0 +1)) (var x0) ▹
        Id (Erased (wk[ 4 ]′ l) (var x3)) [ var x2 ] ([ var x1 ])
      ⊢[]-cong₁ ⊢l =
        lamⱼ′ ok₂ $ lamⱼ′ ok₃ $ lamⱼ′ ok₄ $ lamⱼ′ ok₅ $
        ⊢[]-cong′-3-2-1-0 ⊢l

    []-cong₂ : Term n
    []-cong₂ = lam 𝟘 ([]-cong₁ (level (var x0)))

    opaque

      ▸[]-cong₂ : 𝟘ᶜ ▸[ m ] []-cong₂ {n = n}
      ▸[]-cong₂ =
        lamₘ $ sub (▸[]-cong₁ (level var)) $ begin
          𝟘ᶜ ∙ ⌜ m ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩

          𝟘ᶜ              ∎
        where
        open Tools.Reasoning.PartialOrder ≤ᶜ-poset

    opaque

      ⊢[]-cong₂ :
        let open Erased s in
        Level-allowed →
        Π-allowed 𝟘 q₁ →
        ⊢ Γ →
        Γ ⊢ []-cong₂ ∷
        Π 𝟘 , q₁ ▷ Level ▹
        Π 𝟘 , q₂ ▷ U (level (var x0)) ▹
        Π 𝟘 , q₃ ▷ var x0 ▹
        Π 𝟘 , q₄ ▷ var (x0 +1) ▹
        Π 𝟘 , q₅ ▷ Id (var ((x0 +1) +1)) (var (x0 +1)) (var x0) ▹
        Id (Erased (level (var x4)) (var x3)) [ var x2 ] ([ var x1 ])
      ⊢[]-cong₂ Level-ok ok₁ ⊢Γ =
        lamⱼ′ ok₁ (⊢[]-cong₁ (term-⊢∷ (var₀ (Levelⱼ′ Level-ok ⊢Γ))))

opaque

  -- []-cong is supported for the strength s, the mode m, the variable
  -- context Γ, and the (in a certain sense well-formed) level l, for
  -- certain grades that satisfy certain assumptions, if
  --
  -- * []-cong is allowed for s, or
  -- * Erased is allowed for s and
  --   * erased matches are available for J and 𝟘ᵐ is allowed, or
  --   * m is 𝟘ᵐ, or
  --   * the modality is trivial, or
  --   * equality reflection is allowed.

  []-cong⊎J⊎𝟘ᵐ⊎Trivial⊎Equality-reflection→[]-cong-for-level :
    {Γ : Con Term n} →
    ([]-cong-allowed s × []-cong-allowed-mode s m) ⊎
    Erased-allowed s ×
    (erased-matches-for-J m ≢ none × T 𝟘ᵐ-allowed ⊎
     (∃ λ ok → m PE.≡ 𝟘ᵐ[ ok ]) ⊎
     Trivial ⊎
     Equality-reflection) →
    ε » Γ ⊢ l ∷Level →
    γ ▸[ 𝟘ᵐ? ] l →
    Π-allowed 𝟘 q₁ →
    Π-allowed 𝟘 q₂ →
    Π-allowed 𝟘 q₃ →
    Π-allowed 𝟘 q₄ →
    Has-computing-[]-cong-for-level s m Γ l 𝟘 q₁ 𝟘 q₂ 𝟘 q₃ q₄
  []-cong⊎J⊎𝟘ᵐ⊎Trivial⊎Equality-reflection→[]-cong-for-level
    {l} ok ⊢l ▸l ok₁ ok₂ ok₃ ok₄ =
      ([]-cong₁ l , ▸[]-cong₁ ▸l , ⊢[]-cong₁ ⊢l)
    , λ _ _ _ A t ρ Δ⊇Γ ⊢A ⊢t →
        let ⊇ε = WD.»⊇ε (defn-wf (wf ⊢A)) in
        wk ρ ([]-cong₁ l) ∘⟨ 𝟘 ⟩ A ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ rfl      ⇒*⟨ PE.subst (_⊢_⇒*_∷_ _ _ _)
                                                                           (PE.trans (PE.sym $ Erased.wk-Id-Erased-[]-[] _) $
                                                                            PE.cong₃ Id
                                                                              (PE.cong (flip (Erased.Erased _) _) $
                                                                               PE.trans (subst-wk (wk[ 4 ]′ l)) $
                                                                               PE.trans (subst-wk l) $
                                                                               PE.sym (wk≡subst _ _))
                                                                              PE.refl PE.refl) $
                                                                         β-red-⇒₄′ ok₁ ok₂ ok₃ ok₄
                                                                           (W.wk (W.liftnʷ Δ⊇Γ (∙ ⊢Id-2-1-0′ (WD.defn-wk ⊇ε ⊢l))) $
                                                                            WD.defn-wk ⊇ε (⊢[]-cong′-3-2-1-0 ⊢l))
                                                                           ⊢A ⊢t ⊢t (rflⱼ ⊢t) ⟩⊢
        wk (liftn ρ 4)
          ([]-cong′ ok′ (wk[ 4 ]′ l) (var x3) (var x2) (var x1)
             (var x0))
          [ consSubst (consSubst (consSubst (sgSubst A) t) t) rfl ]  ≡⟨ PE.trans (subst-wk ([]-cong′ ok′ _ _ _ _ _)) $
                                                                        PE.trans ([]-cong′-[] ok′) $
                                                                        PE.cong (λ l → []-cong′ ok′ l _ _ _ _) $
                                                                        PE.trans (subst-wk l) $
                                                                        PE.sym (wk≡subst _ _) ⟩⊢≡

        []-cong′ ok′ (wk ρ l) A t t rfl                              ⇒*⟨ []-cong′-β-⇒* ok′ (inversion-U-Level (wf-⊢ ⊢A)) ⊢t ⟩⊢∎

        rfl                                                          ∎
    where
    open []-cong⊎J⊎𝟘ᵐ⊎Trivial⊎Equality-reflection→[]-cong
           ok ok₁ ok₂ ok₃ ok₄

opaque

  -- []-cong is supported for the strength s, the mode m, and a
  -- well-formed variable context, for certain grades that satisfy
  -- certain assumptions, if Level is allowed and
  --
  -- * []-cong is allowed for s, or
  -- * Erased is allowed for s and
  --   * erased matches are available for J and 𝟘ᵐ is allowed, or
  --   * m is 𝟘ᵐ, or
  --   * the modality is trivial, or
  --   * equality reflection is allowed.

  []-cong⊎J⊎𝟘ᵐ⊎Trivial⊎Equality-reflection→[]-cong :
    {Γ : Con Term n} →
    Level-allowed →
    ([]-cong-allowed s × []-cong-allowed-mode s m) ⊎
    Erased-allowed s ×
    (erased-matches-for-J m ≢ none × T 𝟘ᵐ-allowed ⊎
     (∃ λ ok → m PE.≡ 𝟘ᵐ[ ok ]) ⊎
     Trivial ⊎
     Equality-reflection) →
    ε »⊢ Γ →
    Π-allowed 𝟘 q₁ →
    Π-allowed 𝟘 q₂ →
    Π-allowed 𝟘 q₃ →
    Π-allowed 𝟘 q₄ →
    Π-allowed 𝟘 q₅ →
    Has-computing-[]-cong s m Γ 𝟘 q₁ 𝟘 q₂ 𝟘 q₃ 𝟘 q₄ q₅
  []-cong⊎J⊎𝟘ᵐ⊎Trivial⊎Equality-reflection→[]-cong
    Level-ok ok ⊢Γ ok₁ ok₂ ok₃ ok₄ ok₅ =
      ([]-cong₂ , ▸[]-cong₂ , ⊢[]-cong₂ Level-ok ok₁ ⊢Γ)
    , λ _ _ _ l A t ρ Δ⊇Γ ⊢A ⊢t →
        let ⊇ε = WD.»⊇ε (defn-wf (wf ⊢A)) in
        wk ρ []-cong₂ ∘⟨ 𝟘 ⟩ l ∘⟨ 𝟘 ⟩ A ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ rfl  ⇒*⟨ PE.subst (_⊢_⇒*_∷_ _ _ _)
                                                                            (PE.sym $
                                                                             PE.trans (Erased.Id-Erased-[] _) $
                                                                             PE.cong
                                                                               _[ consSubst (consSubst (consSubst (consSubst (sgSubst l) A) t) t)
                                                                                    rfl ] $
                                                                             Erased.wk-Id-Erased _) $
                                                                          β-red-⇒₅′ ok₁ ok₂ ok₃ ok₄ ok₅
                                                                            (W.wk (W.liftnʷ Δ⊇Γ (∙ ⊢Id-2-1-0 Level-ok (WD.defn-wk ⊇ε ⊢Γ))) $
                                                                             WD.defn-wk ⊇ε (⊢[]-cong′-4-3-2-1-0 Level-ok ⊢Γ))
                                                                            (⊢∷Level→⊢∷Level Level-ok (inversion-U-Level (wf-⊢ ⊢A)))
                                                                            ⊢A ⊢t ⊢t (rflⱼ ⊢t) ⟩⊢
        wk (liftn ρ 5)
          ([]-cong′ ok′ (level (var x4)) (var x3) (var x2) (var x1)
             (var x0))
          [ consSubst
              (consSubst (consSubst (consSubst (sgSubst l) A) t) t)
              rfl ]                                                   ≡⟨ PE.trans (subst-wk ([]-cong′ ok′ _ _ _ _ _)) $
                                                                         []-cong′-[] ok′ ⟩⊢≡

        []-cong′ ok′ (level l) A t t rfl                              ⇒*⟨ []-cong′-β-⇒* ok′ (inversion-U-Level (wf-⊢ ⊢A)) ⊢t ⟩⊢∎

        rfl                                                           ∎
    where
    open []-cong⊎J⊎𝟘ᵐ⊎Trivial⊎Equality-reflection→[]-cong
           ok ok₂ ok₃ ok₄ ok₅

------------------------------------------------------------------------
-- Sometimes []-cong cannot be defined

private opaque

  -- A lemma used below.

  ¬-[]-cong-lemma :
    𝟘ᶜ ▸[ 𝟙ᵐ ] t × ε » Δ ⊢ t ∷ Π 𝟘 , p ▷ B ▹ C →
    let t0 = wk1 t ∘⟨ 𝟘 ⟩ var x0 in
    𝟘ᶜ ▸[ 𝟙ᵐ ] t0 × ε » Δ ∙ B ⊢ t0 ∷ C
  ¬-[]-cong-lemma (▸t , ⊢t) =
    let ⊢B , _ = inversion-ΠΣ (wf-⊢ ⊢t) in
    sub (wkUsage (step id) ▸t ∘ₘ var)
      (begin
         𝟘ᶜ                           ≈˘⟨ ·ᶜ-zeroˡ _ ⟩
         𝟘 ·ᶜ (𝟘ᶜ ∙ ⌜ ⌞ 𝟘 ⌟ ⌝)        ≈˘⟨ +ᶜ-identityˡ _ ⟩
         𝟘ᶜ +ᶜ 𝟘 ·ᶜ (𝟘ᶜ ∙ ⌜ ⌞ 𝟘 ⌟ ⌝)  ∎) ,
    PE.subst (_⊢_∷_ _ _) (wkSingleSubstId _)
      (W.wk₁ ⊢B ⊢t ∘ⱼ var₀ ⊢B)
    where
    open ≤ᶜ-reasoning

opaque

  -- []-cong is not supported for the mode 𝟙ᵐ, the context Γ, the
  -- level l, the type A, the term t, and the grades 𝟘, q₁ and q₂,
  -- assuming that
  --
  -- * the modality's zero is well-behaved,
  --
  -- * erased matches (including the []-cong primitive) are not
  --   allowed (except perhaps for the empty type),
  --
  -- * equality reflection is not allowed,
  --
  -- * η-equality is not allowed for weak unit types unless a certain
  --   condition is satisfied,
  --
  -- * A is a type without η-equality (under an empty definition
  --   context) distinct from Level,
  --
  -- * t is a WHNF (under an empty definition context) that is not a
  --   variable, and
  --
  -- * if erased matches are allowed for the empty type, then ε » Γ is
  --   consistent and t has type A (under ε » Γ).

  ¬-[]-cong-for-value :
    {Γ : Con Term n}
    ⦃ not-ok : No-equality-reflection ⦄
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero 𝕄 ⦄ →
    No-erased-matches TR UR →
    (∀ {p q} →
     Unitʷ-η → Unitʷ-allowed → Unitrec-allowed 𝟙ᵐ p q →
     p ≤ 𝟘) →
    No-η-equality ε A →
    A ≢ Level →
    Whnf ε t →
    (¬ ∃ λ x → t PE.≡ var x) →
    (Emptyrec-allowed 𝟙ᵐ 𝟘 → Consistent (ε » Γ) × ε » Γ ⊢ t ∷ A) →
    ¬ Has-[]-cong-for-value s 𝟙ᵐ Γ l A t 𝟘 q₁ q₂
  ¬-[]-cong-for-value
    {n} {A} {t} {Γ}
    nem Unitʷ-η→ no-η A≢Level t-whnf t≢var consistent (_ , hyp) =
    let ▸[]-cong′ , ⊢[]-cong′ = ¬-[]-cong-lemma (¬-[]-cong-lemma hyp) in
    case red-Id ⦃ ok = included ⦄ ⊢[]-cong′ of λ where
      (_ , rflₙ , ⇒*rfl) →
        t≢var $ Σ.map idᶠ proj₁ $ wk-var $ PE.sym $
        var-only-equal-to-itself (wk-No-η-equality no-η)
           (A≢Level ∘→ wk-Level) (wkWhnf _ t-whnf) $
        []-cong′⁻¹ ⦃ ok = included ⦄
          (sym′ $
           inversion-rfl-Id ⦃ ok = included ⦄ $
           wf-⊢ (subset*Term ⇒*rfl) .proj₂ .proj₂)
      (_ , ne u-ne , []-cong′⇒*u) →
        neutral-not-well-resourced nem
          (λ ok →
             let consistent , ⊢t = consistent ok in
             subst-Consistent (⊢σ ⊢t) consistent)
          PE.refl (ne→ _ u-ne)
          (wf-⊢ (subset*Term []-cong′⇒*u) .proj₂ .proj₂)
          (usagePres*Term₀₁ Unitʷ-η→ (λ ()) ▸[]-cong′ []-cong′⇒*u)
    where
    σ′ : Subst n (2+ n)
    σ′ = consSubst (sgSubst t) rfl

    ⊢σ :
      ε » Γ ⊢ t ∷ A →
      ε » Γ ⊢ˢʷ σ′ ∷ Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0)
    ⊢σ ⊢t =
      →⊢ˢʷ∷∙ (⊢ˢʷ∷-sgSubst ⊢t)
        (PE.subst (_⊢_∷_ _ _) ≡Id-wk1-wk1-0[]₀ (rflⱼ ⊢t))

opaque

  -- A special case of ¬-[]-cong-for-value.

  ¬-[]-cong-for-zero :
    {Γ : Con Term n}
    ⦃ not-ok : No-equality-reflection ⦄
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero 𝕄 ⦄ →
    No-erased-matches TR UR →
    (∀ {p q} →
     Unitʷ-η → Unitʷ-allowed → Unitrec-allowed 𝟙ᵐ p q →
     p ≤ 𝟘) →
    (Emptyrec-allowed 𝟙ᵐ 𝟘 → Consistent (ε » Γ)) →
    ¬ Has-[]-cong-for-value s 𝟙ᵐ Γ zeroᵘₗ ℕ zero 𝟘 q₁ q₂
  ¬-[]-cong-for-zero {Γ} nem Unitʷ-η→ consistent has-[]-cong =
    ¬-[]-cong-for-value nem Unitʷ-η→ ℕₙ (λ ()) zeroₙ (λ { (_ , ()) })
      (λ ok → consistent ok , zeroⱼ ⊢Γ) has-[]-cong
    where
    ⊢Γ : ε »⊢ Γ
    ⊢Γ = wf (has-[]-cong .proj₂ .proj₂)

opaque

  -- If the modality's zero is well-behaved, erased matches (including
  -- the []-cong primitive) are not allowed, equality reflection is
  -- not allowed, and η-equality is not allowed for weak unit types
  -- unless a certain condition is satisfied, then []-cong is not
  -- supported for the mode 𝟙ᵐ and a well-formed type A (in an empty
  -- definition context) without η-equality that is distinct from
  -- Level, if the "p" grades are 𝟘 and, if erased matches are allowed
  -- for the empty type, then A is "consistent".

  ¬-[]-cong-for-type :
    {Γ : Con Term n}
    ⦃ not-ok : No-equality-reflection ⦄
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero 𝕄 ⦄ →
    No-erased-matches TR UR →
    (∀ {p q} →
     Unitʷ-η → Unitʷ-allowed → Unitrec-allowed 𝟙ᵐ p q →
     p ≤ 𝟘) →
    No-η-equality ε A →
    A ≢ Level →
    ε » Γ ⊢ A →
    (Emptyrec-allowed 𝟙ᵐ 𝟘 → Consistent (ε » Γ ∙ A)) →
    ¬ Has-[]-cong-for-type s 𝟙ᵐ Γ l A 𝟘 q₁ 𝟘 q₂ q₃
  ¬-[]-cong-for-type
    {n} {A} {Γ} nem Unitʷ-η→ no-η A≢Level ⊢A consistent (_ , hyp) =
    let ▸[]-cong′ , ⊢[]-cong′ =
          ¬-[]-cong-lemma (¬-[]-cong-lemma (¬-[]-cong-lemma hyp))
    in
    case red-Id ⦃ ok = included ⦄ ⊢[]-cong′ of λ where
      (_ , rflₙ , ⇒*rfl) →
        case var-only-equal-to-itself (wk-No-η-equality no-η)
               (A≢Level ∘→ wk-Level) (ne (var _ _)) $
             []-cong′⁻¹ ⦃ ok = included ⦄
               (inversion-rfl-Id ⦃ ok = included ⦄ $
                wf-⊢ (subset*Term ⇒*rfl) .proj₂ .proj₂)
        of λ ()
      (_ , ne u-ne , []-cong′⇒*u) →
        neutral-not-well-resourced nem
          (subst-Consistent ⊢σ ∘→ consistent)
          PE.refl (ne→ _ u-ne)
          (wf-⊢ (subset*Term []-cong′⇒*u) .proj₂ .proj₂)
          (usagePres*Term₀₁ Unitʷ-η→ (λ ()) ▸[]-cong′ []-cong′⇒*u)
    where
    ⊢Γ : ε »⊢ Γ
    ⊢Γ = wf (hyp .proj₂)

    σ′ : Subst (1+ n) (3+ n)
    σ′ = consSubst (sgSubst (var x0)) rfl

    ⊢σ :
      ε » Γ ∙ A ⊢ˢʷ σ′ ∷
        Γ ∙ A ∙ wk1 A ∙ Id (wk[ 2 ]′ A) (var x1) (var x0)
    ⊢σ =
      let ⊢0 = PE.subst (_⊢_∷_ _ _) (PE.sym $ subst-id _) (var₀ ⊢A) in
      →⊢ˢʷ∷∙ (→⊢ˢʷ∷∙ (⊢ˢʷ∷-idSubst (∙ ⊢A)) ⊢0)
        (rflⱼ $
         PE.subst (_⊢_∷_ _ _)
           (wk1 A [ idSubst ]       ≡⟨ subst-id _ ⟩
            wk1 A                   ≡˘⟨ wk[1+]′-[]₀≡ ⟩
            wk[ 2 ]′ A [ var x0 ]₀  ∎)
           ⊢0)
      where
      open Tools.Reasoning.PropositionalEquality

opaque

  -- If the modality's zero is well-behaved, erased matches (including
  -- the []-cong primitive) are not allowed, equality reflection is
  -- not allowed, and η-equality is not allowed for weak unit types
  -- unless a certain condition is satisfied, then []-cong is not
  -- supported for the mode 𝟙ᵐ, the variable context Γ (which must be
  -- consistent if erased matches are allowed for the empty type), the
  -- well-resourced level l, and certain grades.

  ¬-[]-cong-for-level :
    {Γ : Con Term n}
    ⦃ not-ok : No-equality-reflection ⦄
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero 𝕄 ⦄ →
    No-erased-matches TR UR →
    (∀ {p q} →
     Unitʷ-η → Unitʷ-allowed → Unitrec-allowed 𝟙ᵐ p q →
     p ≤ 𝟘) →
    γ ▸[ 𝟘ᵐ? ] l →
    (Emptyrec-allowed 𝟙ᵐ 𝟘 → Consistent (ε » Γ)) →
    ¬ Has-[]-cong-for-level s 𝟙ᵐ Γ l p₁ q₁ 𝟘 q₂ 𝟘 q₃ q₄
  ¬-[]-cong-for-level
    {n} {l} {s} {p₁} {q₁} {q₂} {q₃} {q₄} {Γ}
    nem Unitʷ-η→ ▸l consistent has-[]-cong =
                                                       $⟨ has-[]-cong ⟩
    Has-[]-cong-for-level s 𝟙ᵐ Γ l p₁ q₁ 𝟘 q₂ 𝟘 q₃ q₄  →⟨ Has-[]-cong-for-level→Has-[]-cong-for-type ⊢A ▸A ⟩
    Has-[]-cong-for-type s 𝟙ᵐ Γ l A′ 𝟘 q₂ 𝟘 q₃ q₄      →⟨ ¬-[]-cong-for-type nem Unitʷ-η→ No-η-equality-A A≢Level (univ ⊢A)
                                                            (subst-Consistent (⊢ˢʷ∷-sgSubst ⊢t) ∘→ consistent) ⟩
    ⊥                                                  □
    where
    ⊢l : ε » Γ ⊢ l ∷Level
    ⊢l = Has-[]-cong-for-level→⊢∷L has-[]-cong

    ⊢Γ : ε »⊢ Γ
    ⊢Γ = wf ⊢l

    u′ : Term n
    u′ = lift zero

    A′ : Term n
    A′ = Id (Lift l ℕ) u′ u′

    t″ : Term n
    t″ = rfl

    ⊢u : ε » Γ ⊢ u′ ∷ Lift l ℕ
    ⊢u = liftⱼ′ ⊢l (zeroⱼ ⊢Γ)

    ⊢A : ε » Γ ⊢ A′ ∷ U l
    ⊢A =
      Idⱼ (conv (Liftⱼ′ ⊢l (ℕⱼ ⊢Γ)) (U-cong-⊢≡ (supᵘₗ-zeroˡ ⊢l))) ⊢u ⊢u

    ⊢t : ε » Γ ⊢ t″ ∷ A′
    ⊢t = rflⱼ ⊢u

    ▸u : 𝟘ᶜ ▸[ m ] u′
    ▸u = liftₘ zeroₘ

    ▸A : 𝟘ᶜ ▸[ m ] A′
    ▸A =
      Idₘ-generalised (Liftₘ ▸l ℕₘ) ▸u ▸u (λ _ → ≤ᶜ-refl)
        (λ _ → begin
           𝟘ᶜ              ≈˘⟨ ≈ᶜ-trans (+ᶜ-congˡ (+ᶜ-identityˡ _)) $
                               +ᶜ-identityˡ _ ⟩
           𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ  ∎)
      where
      open ≤ᶜ-reasoning

    No-η-equality-A : No-η-equality ε A′
    No-η-equality-A = Idₙ

    A≢Level : A′ ≢ Level
    A≢Level ()

opaque

  -- A variant of ¬-[]-cong-for-level.
  --
  -- Note that, if all Π-types are allowed, l is a level literal, and
  -- prodrec is always allowed in erased contexts, then the seven
  -- assumptions after No-erased-matches TR UR and before
  -- Consistent (ε » Δ) are satisfied for the erasure modality with 𝟘ᵐ
  -- (along with 𝟘-well-behaved). If Δ is empty then
  -- Consistent (ε » Δ) also holds.

  ¬-[]-cong-for-level′ :
    ⦃ not-ok : No-equality-reflection ⦄
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero 𝕄 ⦄ →
    No-erased-matches TR UR →
    (∀ {p q} →
     Unitʷ-η → Unitʷ-allowed → Unitrec-allowed 𝟙ᵐ p q →
     p ≤ 𝟘) →
    (s PE.≡ 𝕨 → ¬ T 𝟘ᵐ-allowed → Trivial) →
    (s PE.≡ 𝕨 → Prodrec-allowed 𝟘ᵐ? (𝟘 ∧ 𝟙) 𝟘 𝟘) →
    (s PE.≡ 𝕤 → ¬ T 𝟘ᵐ-allowed → 𝟘 ≤ 𝟙) →
    (Π-allowed p₂ q₂ → Π-allowed 𝟘 q₂′) →
    (Π-allowed p₃ q₃ → Π-allowed 𝟘 q₃′) →
    p₁ ≤ 𝟘 →
    γ ▸[ 𝟘ᵐ? ] l →
    (Emptyrec-allowed 𝟙ᵐ 𝟘 → Consistent (ε » Δ)) →
    ¬ Has-[]-cong-for-level s 𝟙ᵐ Δ l p₁ q₁ p₂ q₂ p₃ q₃ q₄
  ¬-[]-cong-for-level′
    {s} {p₂} {q₂} {q₂′} {p₃} {q₃} {q₃′} {p₁} {l} {Δ} {q₁} {q₄}
    nem Unitʷ-η→ trivial P-ok 𝟘≤𝟙 hyp₂ hyp₃ hyp₁ ▸l consistent =
    Has-[]-cong-for-level s 𝟙ᵐ Δ l p₁ q₁ p₂ q₂ p₃ q₃ q₄  →⟨ Has-[]-cong-for-level-stronger trivial P-ok 𝟘≤𝟙 idᶠ hyp₂ hyp₃ idᶠ
                                                              (≤-trans (≤-reflexive (·-identityˡ _)) hyp₁) (≤-reflexive (·-identityˡ _))
                                                              (≤-reflexive (·-identityˡ _)) ▸l ⟩
    Has-[]-cong-for-level s 𝟙ᵐ Δ l p₁ q₁ 𝟘 q₂′ 𝟘 q₃′ q₄  →⟨ ¬-[]-cong-for-level nem Unitʷ-η→ ▸l consistent ⟩
    ⊥                                                    □

opaque

  -- If the modality's zero is well-behaved, erased matches (including
  -- the []-cong primitive) are not allowed, equality reflection is
  -- not allowed, and η-equality is not allowed for weak unit types
  -- unless a certain condition is satisfied, then []-cong is not
  -- supported for the mode 𝟙ᵐ, a variable context Γ (which must be
  -- consistent if erased matches are allowed for the empty type), and
  -- certain grades.

  ¬-[]-cong :
    {Γ : Con Term n}
    ⦃ not-ok : No-equality-reflection ⦄
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero 𝕄 ⦄ →
    No-erased-matches TR UR →
    (∀ {p q} →
     Unitʷ-η → Unitʷ-allowed → Unitrec-allowed 𝟙ᵐ p q →
     p ≤ 𝟘) →
    (Emptyrec-allowed 𝟙ᵐ 𝟘 → Consistent (ε » Γ)) →
    ¬ Has-[]-cong s 𝟙ᵐ Γ p₁ q₁ p₂ q₂ 𝟘 q₃ 𝟘 q₄ q₅
  ¬-[]-cong
    {n} {s} {p₁} {q₁} {p₂} {q₂} {q₃} {q₄} {q₅} {Γ}
    nem Unitʷ-η→ consistent has-[]-cong@(_ , hyp) =
                                                                $⟨ has-[]-cong ⟩
    Has-[]-cong s 𝟙ᵐ Γ p₁ q₁ p₂ q₂ 𝟘 q₃ 𝟘 q₄ q₅                 →⟨ Has-[]-cong→Has-[]-cong-for-level ⊢l ▸l ⟩
    Has-[]-cong-for-level s 𝟙ᵐ Γ (level l′) p₂ q₂ 𝟘 q₃ 𝟘 q₄ q₅  →⟨ ¬-[]-cong-for-level nem Unitʷ-η→ (level ▸l) consistent ⟩
    ⊥                                                           □
    where
    ⊢Γ : ε »⊢ Γ
    ⊢Γ = wf (hyp .proj₂)

    l′ : Term n
    l′ = zeroᵘ

    ⊢l : ε » Γ ⊢ level l′ ∷Level
    ⊢l = ⊢zeroᵘ ⊢Γ

    ▸l : 𝟘ᶜ ▸[ m ] l′
    ▸l = zeroᵘₘ

opaque

  -- A variant of ¬-[]-cong.
  --
  -- Note that, if all Π-types are allowed and prodrec is always
  -- allowed in erased contexts, then the seven assumptions after
  -- No-erased-matches TR UR and before Consistent (ε » Δ) are
  -- satisfied for the erasure modality with 𝟘ᵐ (along with
  -- 𝟘-well-behaved). If Δ is empty then Consistent (ε » Δ) also
  -- holds.

  ¬-[]-cong′ :
    ⦃ not-ok : No-equality-reflection ⦄
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero 𝕄 ⦄ →
    No-erased-matches TR UR →
    (∀ {p q} →
     Unitʷ-η → Unitʷ-allowed → Unitrec-allowed 𝟙ᵐ p q →
     p ≤ 𝟘) →
    (s PE.≡ 𝕨 → ¬ T 𝟘ᵐ-allowed → Trivial) →
    (s PE.≡ 𝕨 → Prodrec-allowed 𝟘ᵐ? (𝟘 ∧ 𝟙) 𝟘 𝟘) →
    (s PE.≡ 𝕤 → ¬ T 𝟘ᵐ-allowed → 𝟘 ≤ 𝟙) →
    (Π-allowed p₃ q₃ → Π-allowed 𝟘 q₃′) →
    (Π-allowed p₄ q₄ → Π-allowed 𝟘 q₄′) →
    p₁ ≤ ω · p₁ →
    p₂ ≤ 𝟘 →
    (Emptyrec-allowed 𝟙ᵐ 𝟘 → Consistent (ε » Δ)) →
    ¬ Has-[]-cong s 𝟙ᵐ Δ p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ q₅
  ¬-[]-cong′
    {s} {p₃} {q₃} {q₃′} {p₄} {q₄} {q₄′} {p₁} {p₂} {Δ} {q₁} {q₂} {q₅}
    nem Unitʷ-η→ trivial P-ok 𝟘≤𝟙 hyp₃ hyp₄ hyp₁ hyp₂ consistent =
    Has-[]-cong s 𝟙ᵐ Δ p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ q₅  →⟨ Has-[]-cong-stronger trivial P-ok 𝟘≤𝟙 idᶠ idᶠ hyp₃ hyp₄ idᶠ (·-monotoneʳ hyp₁)
                                                        (≤-trans (≤-reflexive (·-identityˡ _)) hyp₂) (≤-reflexive (·-identityˡ _))
                                                        (≤-reflexive (·-identityˡ _)) ⟩
    Has-[]-cong s 𝟙ᵐ Δ p₁ q₁ p₂ q₂ 𝟘 q₃′ 𝟘 q₄′ q₅  →⟨ ¬-[]-cong nem Unitʷ-η→ consistent ⟩
    ⊥                                              □
