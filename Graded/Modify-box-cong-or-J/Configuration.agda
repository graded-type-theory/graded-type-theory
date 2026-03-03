------------------------------------------------------------------------
-- A type used to configure the translation in
-- Graded.Modify-box-cong-or-J, along with some instances
------------------------------------------------------------------------

import Definition.Typed.Restrictions
import Graded.Modality
import Graded.Usage.Restrictions
import Graded.Mode.Instances.Zero-one
open import Graded.Mode.Instances.Zero-one.Variant

module Graded.Modify-box-cong-or-J.Configuration
  {a} {M : Set a}
  (open Graded.Modality M)
  {𝕄 : Modality}
  {variant : Mode-variant 𝕄}
  (open Graded.Mode.Instances.Zero-one variant)
  (open Definition.Typed.Restrictions 𝕄)
  (open Graded.Usage.Restrictions 𝕄 Zero-one-isMode)
  -- The type and usage restrictions used for the source of the
  -- translation.
  (TRₛ : Type-restrictions)
  (URₛ : Usage-restrictions)
  where

open Modality 𝕄
open Mode-variant variant

import Definition.Typed
import Definition.Typed.Inversion
import Definition.Typed.Properties
import Definition.Typed.Substitution
import Definition.Typed.Well-formed
open import Definition.Untyped M
import Definition.Untyped.Erased 𝕄 as Erased
open import Definition.Untyped.Properties M

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
import Graded.Box-cong
import Graded.Derived.Erased.Usage
open import Graded.Erasure.Extraction 𝕄
open import Graded.Erasure.Extraction.Properties 𝕄
import Graded.Erasure.Target as T
open import Graded.Restrictions.Zero-one 𝕄 variant
import Graded.Usage
open import Graded.Usage.Erased-matches
import Graded.Usage.Properties
import Graded.Usage.Properties.Zero-one

open import Tools.Bool hiding (_∧_)
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Level
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum

open Type-restrictions
open Usage-restrictions

private variable
  b                                          : Bool
  n                                          : Nat
  Γ                                          : Cons _ _
  A A₁ A₂ B B₁ B₂ l l₁ l₂
    t t′ t₁ t₂ u u₁ u₂ v v′ v₁ v₂ w w′ w₁ w₂ : Term _
  ρ                                          : Wk _ _
  σ                                          : Subst _ _
  bm                                         : BinderMode
  s                                          : Strength
  γ₁ γ₂ γ₃ γ₄ γ₅ γ₆                          : Conₘ _
  m                                          : Mode
  p q r                                      : M
  sem                                        : Some-erased-matches
  str                                        : T.Strictness

------------------------------------------------------------------------
-- The type

-- A type that is used to configure the translation.

record Configuration : Set (lsuc a) where
  field
    -- Should preservation of reduction be proved?

    preservation-of-reduction : Bool

    -- Should the type preservation results be stated using glassified
    -- definition contexts in the conclusions?

    glassification : Bool

    -- The type and usage restrictions used for the target of the
    -- translation.

    TRₜ : Type-restrictions
    URₜ : Usage-restrictions

  module Tₛ  = Definition.Typed TRₛ
  module Tₜ  = Definition.Typed TRₜ
  module TRₛ = Type-restrictions TRₛ
  module TRₜ = Type-restrictions TRₜ
  module Uₛ  = Graded.Usage URₛ
  module Uₜ  = Graded.Usage URₜ
  module URₛ = Usage-restrictions URₛ
  module URₜ = Usage-restrictions URₜ

  field
    -- Some assumptions related to type restrictions.

    Opacity-allowed-→ :
      ¬ T glassification →
      TRₛ.Opacity-allowed → TRₜ.Opacity-allowed
    level-support-≤ :
      TRₛ.level-support ≤LS TRₜ.level-support
    unfolding-mode-≡ :
      TRₛ.unfolding-mode PE.≡ TRₜ.unfolding-mode
    Unit-allowed-→ :
      TRₛ.Unit-allowed s → TRₜ.Unit-allowed s
    η-for-Unitʷ-≡ :
      TRₛ.η-for-Unitʷ PE.≡ TRₜ.η-for-Unitʷ
    ΠΣ-allowed-→ :
      TRₛ.ΠΣ-allowed bm p q → TRₜ.ΠΣ-allowed bm p q
    K-allowed-→ :
      TRₛ.K-allowed → TRₜ.K-allowed
    Equality-reflection-→ :
      TRₛ.Equality-reflection → TRₜ.Equality-reflection

    -- Some assumptions related to usage restrictions.
    Emptyrec-allowed-→ :
      ∀ m → URₛ.Emptyrec-allowed m p → URₜ.Emptyrec-allowed m p
    Unitrec-allowed-→ :
      ∀ m → URₛ.Unitrec-allowed m p q → URₜ.Unitrec-allowed m p q
    Starˢ-sink-→ :
      URₛ.Starˢ-sink → URₜ.Starˢ-sink
    Prodrec-allowed-→ :
      ∀ m → URₛ.Prodrec-allowed m r p q → URₜ.Prodrec-allowed m r p q
    natrec-mode-≡ :
      URₛ.natrec-mode PE.≡ URₜ.natrec-mode
    Id-erased-⇔ :
      URₛ.Id-erased ⇔ URₜ.Id-erased
    erased-matches-for-K-≡ :
      URₛ.erased-matches-for-K m PE.≡ URₜ.erased-matches-for-K m

  open Tₜ
  open Uₜ

  field
    -- How []-cong should be translated.

    []-cong′ :
      Strength → (_ _ _ _ _ : Term n) → Term n

    -- Assumptions related to []-cong′.

    []-cong′-[] :
      []-cong′ s l A t u v [ σ ] PE.≡
      []-cong′ s (l [ σ ]) (A [ σ ]) (t [ σ ]) (u [ σ ]) (v [ σ ])

    ▸[]-cong′ :
      URₛ.[]-cong-allowed-mode s m →
      γ₁ ▸[ 𝟘ᵐ? ] l →
      γ₂ ▸[ 𝟘ᵐ? ] A →
      γ₃ ▸[ 𝟘ᵐ? ] t →
      γ₄ ▸[ 𝟘ᵐ? ] u →
      γ₅ ▸[ 𝟘ᵐ? ] v →
      𝟘ᶜ ▸[ m ] []-cong′ s l A t u v

    []-cong′-cong :
      let open Erased s in
      TRₛ.[]-cong-allowed s →
      Γ ⊢ l₁ ≡ l₂ ∷Level →
      Γ ⊢ A₁ ≡ A₂ →
      Γ ⊢ t₁ ≡ t₂ ∷ A₁ →
      Γ ⊢ u₁ ≡ u₂ ∷ A₁ →
      Γ ⊢ v₁ ≡ v₂ ∷ Id A₁ t₁ u₁ →
      Γ ⊢ []-cong′ s l₁ A₁ t₁ u₁ v₁ ≡ []-cong′ s l₂ A₂ t₂ u₂ v₂ ∷
        Id (Erased l₁ A₁) [ t₁ ] ([ u₁ ])

    []-cong′-subst :
      T preservation-of-reduction →
      let open Erased s in
      TRₛ.[]-cong-allowed s →
      Γ ⊢ l ∷Level →
      Γ ⊢ v ⇒ v′ ∷ Id A t u →
      Γ ⊢ []-cong′ s l A t u v ⇒* []-cong′ s l A t u v′ ∷
        Id (Erased l A) [ t ] ([ u ])

    []-cong′-β-≡′ :
      ¬ T preservation-of-reduction →
      let open Erased s in
      TRₛ.[]-cong-allowed s →
      Γ ⊢ l ∷Level →
      Γ ⊢ t ∷ A →
      Γ ⊢ []-cong′ s l A t t rfl ≡ rfl ∷ Id (Erased l A) [ t ] ([ t ])

    []-cong′-β-⇒* :
      T preservation-of-reduction →
      let open Erased s in
      TRₛ.[]-cong-allowed s →
      Γ ⊢ l ∷Level →
      Γ ⊢ t ≡ t′ ∷ A →
      Γ ⊢ []-cong′ s l A t t′ rfl ⇒* rfl ∷
        Id (Erased l A) [ t ] ([ t′ ])

    erase-[]-cong′ :
      erase′ b str ([]-cong′ s l A t u v) PE.≡ loop? str

    -- How J should be translated.

    J′ :
      (_ _ : M) (_ _ : Term n) → Term (2+ n) → (_ _ _ : Term n) → Term n

    -- Assumptions related to J′.

    J′-[] :
      J′ p q A t B u v w [ σ ] PE.≡
      J′ p q (A [ σ ]) (t [ σ ]) (B [ σ ⇑[ 2 ] ]) (u [ σ ]) (v [ σ ])
        (w [ σ ])

    ▸J′ :
      URₛ.erased-matches-for-J m ≤ᵉᵐ some →
      (URₛ.erased-matches-for-J m PE.≡ some → ¬ (p PE.≡ 𝟘 × q PE.≡ 𝟘)) →
      γ₁ ▸[ 𝟘ᵐ? ] A →
      γ₂ ▸[ m ] t →
      γ₃ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · q ▸[ m ] B →
      γ₄ ▸[ m ] u →
      γ₅ ▸[ m ] v →
      γ₆ ▸[ m ] w →
      ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆) ▸[ m ] J′ p q A t B u v w

    ▸J′₀₁ :
      URₛ.erased-matches-for-J m PE.≡ some →
      γ₁ ▸[ 𝟘ᵐ? ] A →
      γ₂ ▸[ 𝟘ᵐ? ] t →
      γ₃ ∙ 𝟘 ∙ 𝟘 ▸[ m ] B →
      γ₄ ▸[ m ] u →
      γ₅ ▸[ 𝟘ᵐ? ] v →
      γ₆ ▸[ 𝟘ᵐ? ] w →
      ω ·ᶜ (γ₃ +ᶜ γ₄) ▸[ m ] J′ 𝟘 𝟘 A t B u v w

    ▸J′₀₂ :
      URₛ.erased-matches-for-J m PE.≡ all →
      γ₁ ▸[ 𝟘ᵐ? ] A →
      γ₂ ▸[ 𝟘ᵐ? ] t →
      γ₃ ∙ ⌜ 𝟘ᵐ? ⌝ · p ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] B →
      γ₄ ▸[ m ] u →
      γ₅ ▸[ 𝟘ᵐ? ] v →
      γ₆ ▸[ 𝟘ᵐ? ] w →
      γ₄ ▸[ m ] J′ p q A t B u v w

    J′-cong :
      Γ ⊢ A₁ ≡ A₂ →
      Γ ⊢ t₁ ≡ t₂ ∷ A₁ →
      Γ »∙ A₁ »∙ Id (wk1 A₁) (wk1 t₁) (var x0) ⊢ B₁ ≡ B₂ →
      Γ ⊢ u₁ ≡ u₂ ∷ B₁ [ t₁ , rfl ]₁₀ →
      Γ ⊢ v₁ ≡ v₂ ∷ A₁ →
      Γ ⊢ w₁ ≡ w₂ ∷ Id A₁ t₁ v₁ →
      Γ ⊢ J′ p q A₁ t₁ B₁ u₁ v₁ w₁ ≡ J′ p q A₂ t₂ B₂ u₂ v₂ w₂ ∷
        B₁ [ v₁ , w₁ ]₁₀

    J′-subst :
      T preservation-of-reduction →
      Γ »∙ A »∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
      Γ ⊢ u ∷ B [ t , rfl ]₁₀ →
      Γ ⊢ w ⇒ w′ ∷ Id A t v →
      Γ ⊢ J′ p q A t B u v w ⇒* J′ p q A t B u v w′ ∷ B [ v , w ]₁₀

    J′-β-≡′ :
      ¬ T preservation-of-reduction →
      Γ ⊢ t ∷ A →
      Γ »∙ A »∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
      Γ ⊢ u ∷ B [ t , rfl ]₁₀ →
      Γ ⊢ J′ p q A t B u t rfl ≡ u ∷ B [ t , rfl ]₁₀

    J′-β-⇒* :
      T preservation-of-reduction →
      Γ ⊢ t ≡ t′ ∷ A →
      Γ »∙ A »∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
      Γ ⊢ u ∷ B [ t , rfl ]₁₀ →
      Γ ⊢ J′ p q A t B u t′ rfl ⇒* u ∷ B [ t , rfl ]₁₀

    erase-J′ :
      erase′ b str (J′ p q A t B u v w) PE.≡ erase′ b str u

  ----------------------------------------------------------------------
  -- Some admissible results related to type restrictions

  opaque

    -- Level-allowed holds for the source if and only if it holds for
    -- the target.

    Level-allowed-⇔ : TRₛ.Level-allowed ⇔ TRₜ.Level-allowed
    Level-allowed-⇔ =
      TRₛ.Level-allowed                     ⇔⟨ TRₛ.Level-allowed⇔≢ ⟩
      TRₛ.level-support PE.≢ only-literals  ⇔⟨ ≤LS→≢only-literals⇔≢only-literals level-support-≤ ⟩
      TRₜ.level-support PE.≢ only-literals  ⇔˘⟨ TRₜ.Level-allowed⇔≢ ⟩
      TRₜ.Level-allowed                     □⇔

  opaque

    -- Level-is-small holds for the target if it holds for the source.

    Level-is-small-→ : TRₛ.Level-is-small → TRₜ.Level-is-small
    Level-is-small-→ =
      TRₛ.Level-is-small                       ⇔⟨ TRₛ.Level-is-small⇔ ⟩→
      TRₛ.level-support PE.≡ level-type small  →⟨ ≤LS→≡small→≡small level-support-≤ ⟩
      TRₜ.level-support PE.≡ level-type small  ⇔˘⟨ TRₜ.Level-is-small⇔ ⟩→
      TRₜ.Level-is-small                       □

  opaque

    -- Unitʷ-η holds for the source if and only if it holds for the
    -- target.

    Unitʷ-η-⇔ : TRₛ.Unitʷ-η ⇔ TRₜ.Unitʷ-η
    Unitʷ-η-⇔ = PE.subst (_⇔_ _) (PE.cong T η-for-Unitʷ-≡) id⇔

  opaque

    -- Unit-with-η s holds for the source if and only if it holds for
    -- the target.

    Unit-with-η-⇔ : TRₛ.Unit-with-η s ⇔ TRₜ.Unit-with-η s
    Unit-with-η-⇔ = id⇔ ⊎-cong-⇔ Unitʷ-η-⇔

  ----------------------------------------------------------------------
  -- Some admissible weakening lemmas

  opaque

    -- A weakening lemma for []-cong′.

    wk-[]-cong′ :
      wk ρ ([]-cong′ s l A t u v) PE.≡
      []-cong′ s (wk ρ l) (wk ρ A) (wk ρ t) (wk ρ u) (wk ρ v)
    wk-[]-cong′ {ρ} {s} {l} {A} {t} {u} {v} =
      wk ρ ([]-cong′ s l A t u v)                                       ≡⟨ wk≡subst _ _ ⟩

      []-cong′ s l A t u v [ toSubst ρ ]                                ≡⟨ []-cong′-[] ⟩

      []-cong′ s (l [ toSubst ρ ]) (A [ toSubst ρ ]) (t [ toSubst ρ ])
        (u [ toSubst ρ ]) (v [ toSubst ρ ])                             ≡˘⟨ PE.cong₅ ([]-cong′ _) (wk≡subst _ _) (wk≡subst _ _) (wk≡subst _ _)
                                                                              (wk≡subst _ _) (wk≡subst _ _) ⟩
      []-cong′ s (wk ρ l) (wk ρ A) (wk ρ t) (wk ρ u) (wk ρ v)           ∎
      where
      open Tools.Reasoning.PropositionalEquality

  opaque

    -- A weakening lemma for J′.

    wk-J′ :
      wk ρ (J′ p q A t B u v w) PE.≡
      J′ p q (wk ρ A) (wk ρ t) (wk (liftn ρ 2) B) (wk ρ u) (wk ρ v)
        (wk ρ w)
    wk-J′ {ρ} {p} {q} {A} {t} {B} {u} {v} {w} =
      wk ρ (J′ p q A t B u v w)                                          ≡⟨ wk≡subst _ _ ⟩

      J′ p q A t B u v w [ toSubst ρ ]                                   ≡⟨ J′-[] ⟩

      J′ p q (A [ toSubst ρ ]) (t [ toSubst ρ ])
        (B [ toSubst ρ ⇑[ 2 ] ]) (u [ toSubst ρ ]) (v [ toSubst ρ ])
        (w [ toSubst ρ ])                                                ≡˘⟨ PE.cong₄ (J′ _ _ _ _)
                                                                               (substVar-to-subst (toSubst-liftn 2) B)
                                                                               PE.refl PE.refl PE.refl ⟩
      J′ p q (A [ toSubst ρ ]) (t [ toSubst ρ ])
        (B [ toSubst (liftn ρ 2) ]) (u [ toSubst ρ ]) (v [ toSubst ρ ])
        (w [ toSubst ρ ])                                                ≡˘⟨ PE.cong₆ (J′ _ _) (wk≡subst _ _) (wk≡subst _ _) (wk≡subst _ _)
                                                                               (wk≡subst _ _) (wk≡subst _ _) (wk≡subst _ _) ⟩
      J′ p q (wk ρ A) (wk ρ t) (wk (liftn ρ 2) B) (wk ρ u) (wk ρ v)
        (wk ρ w)                                                         ∎
      where
      open Tools.Reasoning.PropositionalEquality

  ----------------------------------------------------------------------
  -- Some admissible typing, equality and reduction rules

  open Definition.Typed.Inversion TRₜ
  open Definition.Typed.Properties TRₜ hiding ([]-cong′)
  open Definition.Typed.Substitution TRₜ
  open Definition.Typed.Well-formed TRₜ

  opaque

    -- A typing rule for []-cong′.

    ⊢[]-cong′ :
      let open Erased s in
      TRₛ.[]-cong-allowed s →
      Γ ⊢ l ∷Level →
      Γ ⊢ v ∷ Id A t u →
      Γ ⊢ []-cong′ s l A t u v ∷ Id (Erased l A) [ t ] ([ u ])
    ⊢[]-cong′ ok ⊢l ⊢v =
      let ⊢A , ⊢t , ⊢u = inversion-Id (wf-⊢∷ ⊢v) in
      wf-⊢≡∷
        ([]-cong′-cong ok (refl-⊢≡∷L ⊢l) (refl ⊢A) (refl ⊢t) (refl ⊢u)
           (refl ⊢v))
        .proj₂ .proj₁

  opaque

    -- An equality rule for []-cong′.

    []-cong′-β-≡ :
      let open Erased s in
      TRₛ.[]-cong-allowed s →
      Γ ⊢ l ∷Level →
      Γ ⊢ t ∷ A →
      Γ ⊢ []-cong′ s l A t t rfl ≡ rfl ∷ Id (Erased l A) [ t ] ([ t ])
    []-cong′-β-≡ ok ⊢l ⊢t =
      case T? preservation-of-reduction of λ where
        (yes pres)   → subset*Term ([]-cong′-β-⇒* pres ok ⊢l (refl ⊢t))
        (no no-pres) → []-cong′-β-≡′ no-pres ok ⊢l ⊢t

  opaque

    -- A reduction rule for []-cong′.

    []-cong′-subst* :
      T preservation-of-reduction →
      let open Erased s in
      TRₛ.[]-cong-allowed s →
      Γ ⊢ l ∷Level →
      Γ ⊢ v ⇒* v′ ∷ Id A t u →
      Γ ⊢ []-cong′ s l A t u v ⇒* []-cong′ s l A t u v′ ∷
        Id (Erased l A) [ t ] ([ u ])
    []-cong′-subst* pres ok ⊢l = λ where
      (id ⊢v) →
        id (⊢[]-cong′ ok ⊢l ⊢v)
      (v⇒v′ ⇨ v′⇒*v″) →
        []-cong′-subst pres ok ⊢l v⇒v′ ⇨∷*
        []-cong′-subst* pres ok ⊢l v′⇒*v″

  opaque

    -- A typing rule for J′.

    ⊢J′ :
      Γ »∙ A »∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
      Γ ⊢ u ∷ B [ t , rfl ]₁₀ →
      Γ ⊢ w ∷ Id A t v →
      Γ ⊢ J′ p q A t B u v w ∷ B [ v , w ]₁₀
    ⊢J′ ⊢B ⊢u ⊢w =
      let ⊢A , ⊢t , ⊢v = inversion-Id (wf-⊢∷ ⊢w) in
      wf-⊢≡∷
        (J′-cong (refl ⊢A) (refl ⊢t) (refl ⊢B) (refl ⊢u) (refl ⊢v)
           (refl ⊢w))
        .proj₂ .proj₁

  opaque

    -- An equality rule for J.

    J′-β-≡ :
      Γ ⊢ t ∷ A →
      Γ »∙ A »∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
      Γ ⊢ u ∷ B [ t , rfl ]₁₀ →
      Γ ⊢ J′ p q A t B u t rfl ≡ u ∷ B [ t , rfl ]₁₀
    J′-β-≡ ⊢t ⊢B ⊢u =
      case T? preservation-of-reduction of λ where
        (yes pres)   → subset*Term (J′-β-⇒* pres (refl ⊢t) ⊢B ⊢u)
        (no no-pres) → J′-β-≡′ no-pres ⊢t ⊢B ⊢u

  opaque

    -- A reduction rule for J′.

    J′-subst* :
      T preservation-of-reduction →
      Γ »∙ A »∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
      Γ ⊢ u ∷ B [ t , rfl ]₁₀ →
      Γ ⊢ w ⇒* w′ ∷ Id A t v →
      Γ ⊢ J′ p q A t B u v w ⇒* J′ p q A t B u v w′ ∷ B [ v , w ]₁₀
    J′-subst* pres ⊢B ⊢u = λ where
      (id ⊢w) →
        id (⊢J′ ⊢B ⊢u ⊢w)
      (w⇒w′ ⇨ w′⇒*w″) →
        let w≡w′       = subsetTerm w⇒w′
            _ , _ , ⊢v = inversion-Id (wf-⊢≡∷ w≡w′ .proj₁)
        in
        J′-subst pres ⊢B ⊢u w⇒w′ ⇨∷*
        conv* (J′-subst* pres ⊢B ⊢u w′⇒*w″)
          (substTypeEq₂ (refl ⊢B) (refl ⊢v) $
           PE.subst (_⊢_≡_∷_ _ _ _) ≡Id-wk1-wk1-0[]₀ $
           sym′ w≡w′)

------------------------------------------------------------------------
-- Some configurations

private opaque

  -- A lemma used below.

  ≡-not-none-preserved :
    URₛ .erased-matches-for-J m PE.≡ not-none sem →
    no-[]-cong-UR URₛ .erased-matches-for-J m PE.≡ not-none sem
  ≡-not-none-preserved {m} hyp with URₛ .erased-matches-for-J m
  ≡-not-none-preserved     hyp | not-none _ = hyp
  ≡-not-none-preserved     ()  | none

opaque

  -- A translation that replaces every occurrence of []-cong with
  -- []-cong-J.
  --
  -- The translation uses the assumption that 𝟘ᵐ is allowed (given a
  -- certain assumption). This assumption is at the time of writing
  -- only used to prove that the translation is usage-preserving.

  remove-[]-cong :
    (∀ {s} m →
     Usage-restrictions.[]-cong-allowed-mode URₛ s m → T 𝟘ᵐ-allowed) →
    Configuration
  remove-[]-cong 𝟘ᵐ-ok = λ where
      .preservation-of-reduction       → true
      .glassification                  → false
      .Configuration.TRₜ               → TRₜ
      .Configuration.URₜ               → URₜ
      .Opacity-allowed-→ _             → idᶠ
      .level-support-≤                 → refl-≤LS
      .unfolding-mode-≡                → PE.refl
      .Unit-allowed-→                  → idᶠ
      .η-for-Unitʷ-≡                   → PE.refl
      .ΠΣ-allowed-→                    → idᶠ
      .K-allowed-→                     → idᶠ
      .Equality-reflection-→           → idᶠ
      .Emptyrec-allowed-→ _            → idᶠ
      .Unitrec-allowed-→ _             → idᶠ
      .Starˢ-sink-→                    → idᶠ
      .Prodrec-allowed-→ _             → idᶠ
      .natrec-mode-≡                   → PE.refl
      .Id-erased-⇔                     → id⇔
      .erased-matches-for-K-≡          → PE.refl
      .[]-cong′                        → []-cong-J
      .[]-cong′-[]                     → []-cong-J-[]
      .▸[]-cong′ {m} ok ▸l ▸A ▸t ▸u ▸v →
        ▸[]-cong-J {ok = 𝟘ᵐ-ok m ok}
          (some-erased-matches-allowed .proj₂) (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸l)
          (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸A) (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸t) (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸u)
          (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸v)
      .[]-cong′-cong ok →
        []-cong-J-cong (TRₛ .[]-cong→Erased ok)
      .[]-cong′-subst _ ok ⊢l v⇒v′ →
        redMany ([]-cong-J-subst (TRₛ .[]-cong→Erased ok) ⊢l v⇒v′)
      .[]-cong′-β-≡′ ¬⊤ →
        ⊥-elim (¬⊤ _)
      .[]-cong′-β-⇒* _ ok ⊢l t≡t′ →
        redMany ([]-cong-J-β-⇒′ (TRₛ .[]-cong→Erased ok) ⊢l t≡t′)
      .erase-[]-cong′ →
        erase-[]-cong-J
      .J′                    → J
      .J′-[]                 → PE.refl
      .▸J′ _ _               → Jₘ-generalised
      .▸J′₀₁ ok              → J₀ₘ₁ (≡-not-none-preserved ok)
                                 PE.refl PE.refl
      .▸J′₀₂ ok              → J₀ₘ₂ (≡-not-none-preserved ok)
      .J′-cong               → J-cong′
      .J′-subst _ ⊢B ⊢u w⇒w′ → redMany (J-subst′ ⊢B ⊢u w⇒w′)
      .J′-β-≡′ ¬⊤            → ⊥-elim (¬⊤ _)
      .J′-β-⇒* _ t≡t′ ⊢B ⊢u  → redMany (J-β-⇒ t≡t′ ⊢B ⊢u)
      .erase-J′              → PE.refl
    where
    TRₜ : Type-restrictions
    TRₜ = no-[]-cong-TR TRₛ

    URₜ : Usage-restrictions
    URₜ = no-[]-cong-UR URₛ

    open Configuration hiding (TRₜ; URₜ)
    open Definition.Typed TRₜ
    open Definition.Typed.Properties TRₜ hiding ([]-cong′)
    open Graded.Box-cong TRₜ URₜ
    open Graded.Usage URₜ
    open Graded.Usage.Properties URₜ
    open Graded.Usage.Properties.Zero-one variant URₜ

    some-erased-matches-allowed :
      ∃ λ sem → URₜ .erased-matches-for-J m PE.≡ not-none sem
    some-erased-matches-allowed {m} with URₛ .erased-matches-for-J m
    … | none       = _ , PE.refl
    … | not-none _ = _ , PE.refl

opaque

  -- A translation that replaces every occurrence of J 𝟘 𝟘 with Jᵉ.
  --
  -- The translation uses the assumption that 𝟘ᵐ is allowed, and that
  -- at most "some" erased matches are allowed for J when the mode is
  -- 𝟙ᵐ (according to URₛ). The latter assumption is at the time of
  -- writing only used to prove that the translation is
  -- usage-preserving. The former assumption is also used to prove
  -- that the translation is type-preserving, but for that it would
  -- suffice to assume that the modality is non-trivial.
  --
  -- Preservation of reduction is not proved for this translation,
  -- because "Jᵉ-subst" can not be proved (assuming that the
  -- meta-theory is consistent), see
  -- Definition.Typed.Properties.Admissible.Erased.¬-Jᵉ-subst-⇒*.

  remove-J-𝟘-𝟘 :
    ⦃ ok : T 𝟘ᵐ-allowed ⦄ →
    Prodrec-allowed URₛ 𝟘ᵐ? (𝟘 ∧ 𝟙) 𝟘 𝟘 →
    Usage-restrictions.erased-matches-for-J URₛ 𝟙ᵐ ≤ᵉᵐ some →
    Configuration
  remove-J-𝟘-𝟘 ⦃ ok = 𝟘ᵐ-ok ⦄ P-ok ≤some = λ where
      .preservation-of-reduction            → false
      .glassification                       → false
      .Configuration.TRₜ                    → TRₜ
      .Configuration.URₜ                    → URₜ
      .Opacity-allowed-→ _                  → idᶠ
      .level-support-≤                      → refl-≤LS
      .unfolding-mode-≡                     → PE.refl
      .Unit-allowed-→                       → inj₁
      .η-for-Unitʷ-≡                        → PE.refl
      .ΠΣ-allowed-→ {bm = BMΣ _}            → inj₁
      .ΠΣ-allowed-→ {bm = BMΠ}              → idᶠ
      .K-allowed-→                          → idᶠ
      .Equality-reflection-→                → idᶠ
      .Emptyrec-allowed-→ _                 → idᶠ
      .Unitrec-allowed-→ _                  → idᶠ
      .Starˢ-sink-→                         → idᶠ
      .Prodrec-allowed-→ _                  → idᶠ
      .natrec-mode-≡                        → PE.refl
      .Id-erased-⇔                          → id⇔
      .erased-matches-for-K-≡               → PE.refl
      .[]-cong′                             → []-cong
      .[]-cong′-[]                          → PE.refl
      .▸[]-cong′ ok ▸l ▸A ▸t ▸u ▸v →
        []-congₘ ▸l ▸A ▸t ▸u ▸v (inj₁ ok)
      .[]-cong′-cong _ l₁≡l₂ A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ →
        []-cong-cong l₁≡l₂ A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ non-trivial
      .[]-cong′-subst _ _ ⊢l v⇒v′ →
        redMany $ []-cong-subst ⊢l v⇒v′ non-trivial
      .[]-cong′-β-≡′ _ _ ⊢l ⊢t →
        []-cong-β-≡ ⊢l (refl ⊢t) non-trivial
      .[]-cong′-β-⇒* ()
      .erase-[]-cong′ →
        PE.refl
      .J′ p q      → J″       (is-𝟘? p ×-dec is-𝟘? q)
      .J′-[]       → J″-[]    (is-𝟘? _ ×-dec _)
      .▸J′ _ _     → ▸J″      (is-𝟘? _ ×-dec _)
      .▸J′₀₁ _     → ▸J″₀₁    (is-𝟘? _ ×-dec _)
      .▸J′₀₂       → ▸J″₀₂    (is-𝟘? _ ×-dec _)
      .J′-cong     → J″-cong  (is-𝟘? _ ×-dec _)
      .J′-subst ()
      .J′-β-≡′ _   → J″-β-≡′  (is-𝟘? _ ×-dec _)
      .J′-β-⇒* ()
      .erase-J′    → erase-J″ (is-𝟘? _ ×-dec _)
    where
    TRₜ : Type-restrictions
    TRₜ = []-cong-TR TRₛ

    URₜ : Usage-restrictions
    URₜ = []-cong-UR URₛ

    open Configuration hiding (TRₜ; URₜ)
    open Definition.Typed TRₜ
    open Definition.Typed.Properties TRₜ hiding ([]-cong′)
    open Graded.Derived.Erased.Usage URₜ 𝕨
    open Graded.Usage URₜ
    open Graded.Usage.Properties URₜ
    open Graded.Usage.Properties.Zero-one variant URₜ
    open ≤ᶜ-reasoning

    opaque

      non-trivial : ¬ Trivial
      non-trivial =
        Has-well-behaved-zero.non-trivial (𝟘-well-behaved 𝟘ᵐ-ok)

    opaque

      []-cong-ok : ∀ m → []-cong-allowed-mode URₜ 𝕨 m
      []-cong-ok _ = inj₂ non-trivial

    J″ :
      Dec (p PE.≡ 𝟘 × q PE.≡ 𝟘) → Term n → Term n → Term (2+ n) →
      Term n → Term n → Term n → Term n
    J″         (yes _) = Erased.Jᵉ 𝕨
    J″ {p} {q} (no _)  = J p q

    opaque

      J″-[] :
        (d : Dec (p PE.≡ 𝟘 × q PE.≡ 𝟘)) →
        J″ d A t B u v w [ σ ] PE.≡
        J″ d (A [ σ ]) (t [ σ ]) (B [ σ ⇑[ 2 ] ]) (u [ σ ]) (v [ σ ])
          (w [ σ ])
      J″-[] = λ where
        (yes _) → Erased.Jᵉ-[] _
        (no _)  → PE.refl

    opaque

      ▸J″ :
        (d : Dec (p PE.≡ 𝟘 × q PE.≡ 𝟘)) →
        γ₁ ▸[ 𝟘ᵐ? ] A →
        γ₂ ▸[ m ] t →
        γ₃ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · q ▸[ m ] B →
        γ₄ ▸[ m ] u →
        γ₅ ▸[ m ] v →
        γ₆ ▸[ m ] w →
        ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆) ▸[ m ] J″ d A t B u v w
      ▸J″ {γ₂} {m} {γ₃} {γ₄} {γ₅} {γ₆} = λ where
        (no _) →
          Jₘ-generalised
        (yes (PE.refl , PE.refl)) ▸A ▸t ▸B ▸u ▸v ▸w →
          sub
            (▸Jᵉ (λ _ → ⊥-elim ∘→ 𝟘ᵐ-allowed→¬Trivialᵐ 𝟘ᵐ-ok)
               (λ _ → P-ok) (λ ()) ([]-cong-ok m) ▸A (▸-𝟘ᵐ? ▸t .proj₂)
               (sub ▸B $ begin
                  γ₃ ∙ 𝟘 ∙ 𝟘                  ≈˘⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ⟩
                  γ₃ ∙ ⌜ m ⌝ · 𝟘 ∙ ⌜ m ⌝ · 𝟘  ∎)
               ▸u (▸-𝟘ᵐ? ▸v .proj₂) (▸-𝟘ᵐ? ▸w .proj₂))
            (begin
               ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆)  ≤⟨ ω·ᶜ+ᶜ≤ω·ᶜʳ ⟩
               ω ·ᶜ (γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆)        ≈⟨ ·ᶜ-distribˡ-+ᶜ _ _ _ ⟩
               ω ·ᶜ γ₃ +ᶜ ω ·ᶜ (γ₄ +ᶜ γ₅ +ᶜ γ₆)   ≤⟨ +ᶜ-monotoneʳ ω·ᶜ+ᶜ≤ω·ᶜˡ ⟩
               ω ·ᶜ γ₃ +ᶜ ω ·ᶜ γ₄                 ≈˘⟨ ·ᶜ-distribˡ-+ᶜ _ _ _ ⟩
               ω ·ᶜ (γ₃ +ᶜ γ₄)                    ∎)

    opaque

      ▸J″₀₁ :
        (d : Dec (𝟘 PE.≡ 𝟘 × 𝟘 PE.≡ 𝟘)) →
        γ₁ ▸[ 𝟘ᵐ? ] A →
        γ₂ ▸[ 𝟘ᵐ? ] t →
        γ₃ ∙ 𝟘 ∙ 𝟘 ▸[ m ] B →
        γ₄ ▸[ m ] u →
        γ₅ ▸[ 𝟘ᵐ? ] v →
        γ₆ ▸[ 𝟘ᵐ? ] w →
        ω ·ᶜ (γ₃ +ᶜ γ₄) ▸[ m ] J″ d A t B u v w
      ▸J″₀₁ {m} = λ where
        (yes _) →
          ▸Jᵉ (λ _ → ⊥-elim ∘→ 𝟘ᵐ-allowed→¬Trivialᵐ 𝟘ᵐ-ok) (λ _ → P-ok) (λ ()) ([]-cong-ok m)
        (no not-equal) →
          ⊥-elim $ not-equal (PE.refl , PE.refl)

    opaque

      ▸J″₀₂ :
        (d : Dec (p PE.≡ 𝟘 × q PE.≡ 𝟘)) →
        URₛ .erased-matches-for-J m PE.≡ all →
        γ₁ ▸[ 𝟘ᵐ? ] A →
        γ₂ ▸[ 𝟘ᵐ? ] t →
        γ₃ ∙ ⌜ 𝟘ᵐ? ⌝ · p ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] B →
        γ₄ ▸[ m ] u →
        γ₅ ▸[ 𝟘ᵐ? ] v →
        γ₆ ▸[ 𝟘ᵐ? ] w →
        γ₄ ▸[ m ] J″ d A t B u v w
      ▸J″₀₂ {m = 𝟙ᵐ} _ ok =
        ⊥-elim $ PE.subst (flip _≤ᵉᵐ_ _) ok ≤some
      ▸J″₀₂ {p} {q} {m = 𝟘ᵐ[ ok ]} {A} {t} {γ₃} {B} {γ₄} {u} {v} {w}
        d _ ▸A ▸t ▸B ▸u ▸v ▸w =
        let 𝟘·∙𝟘·-lemma = begin
              γ₃ ∙ 𝟘 · p ∙ 𝟘 · q              ≈˘⟨ ≈ᶜ-refl ∙ ·-congʳ (⌜𝟘ᵐ?⌝≡𝟘 ok) ∙ ·-congʳ (⌜𝟘ᵐ?⌝≡𝟘 ok) ⟩
              γ₃ ∙ ⌜ 𝟘ᵐ? ⌝ · p ∙ ⌜ 𝟘ᵐ? ⌝ · q  ∎

            ▸J″ :
              (d : Dec (p PE.≡ 𝟘 × q PE.≡ 𝟘)) →
              𝟘ᶜ ▸[ 𝟘ᵐ[ ok ] ] J″ d A t B u v w
            ▸J″ = λ where
              (yes _) →
                ▸-𝟘₀₁ $ ▸Jᵉ (λ _ → ⊥-elim ∘→ 𝟘ᵐ-allowed→¬Trivialᵐ 𝟘ᵐ-ok) (λ _ → P-ok) (λ ())
                  ([]-cong-ok 𝟘ᵐ[ ok ]) ▸A ▸t
                  (sub (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸B) $ begin
                     γ₃ ∙ 𝟘 ∙ 𝟘                      ≈˘⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ∙ ·-zeroˡ _ ⟩
                     γ₃ ∙ 𝟘 · p ∙ 𝟘 · q              ≤⟨ 𝟘·∙𝟘·-lemma ⟩
                     γ₃ ∙ ⌜ 𝟘ᵐ? ⌝ · p ∙ ⌜ 𝟘ᵐ? ⌝ · q  ∎)
                  ▸u ▸v ▸w
              (no _) →
                ▸-𝟘₀₁ $
                Jₘ-generalised (▸-𝟘ᵐ? ▸A .proj₂) (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸t)
                  (sub (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸B) 𝟘·∙𝟘·-lemma) ▸u
                  (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸v) (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸w)
        in
        sub (▸J″ d) $ begin
          γ₄  ≤⟨ ▸-𝟘ᵐ₀₁ ▸u ⟩
          𝟘ᶜ  ∎

    opaque

      J″-cong :
        (d : Dec (p PE.≡ 𝟘 × q PE.≡ 𝟘)) →
        Γ ⊢ A₁ ≡ A₂ →
        Γ ⊢ t₁ ≡ t₂ ∷ A₁ →
        Γ »∙ A₁ »∙ Id (wk1 A₁) (wk1 t₁) (var x0) ⊢ B₁ ≡ B₂ →
        Γ ⊢ u₁ ≡ u₂ ∷ B₁ [ t₁ , rfl ]₁₀ →
        Γ ⊢ v₁ ≡ v₂ ∷ A₁ →
        Γ ⊢ w₁ ≡ w₂ ∷ Id A₁ t₁ v₁ →
        Γ ⊢ J″ d A₁ t₁ B₁ u₁ v₁ w₁ ≡ J″ d A₂ t₂ B₂ u₂ v₂ w₂ ∷
          B₁ [ v₁ , w₁ ]₁₀
      J″-cong = λ where
        (yes _) → Jᵉ-cong non-trivial
        (no _)  → J-cong′

    opaque

      -- This reduction lemma can be proved.

      J″-β-⇒* :
        (d : Dec (p PE.≡ 𝟘 × q PE.≡ 𝟘)) →
        Γ ⊢ t ∷ A →
        Γ »∙ A »∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
        Γ ⊢ u ∷ B [ t , rfl ]₁₀ →
        Γ ⊢ J″ d A t B u t rfl ⇒* u ∷ B [ t , rfl ]₁₀
      J″-β-⇒* = λ where
        (yes _)         → Jᵉ-⇒* non-trivial
        (no _) ⊢t ⊢B ⊢u → redMany (J-β-⇒ (refl ⊢t) ⊢B ⊢u)

    opaque

      J″-β-≡′ :
        (d : Dec (p PE.≡ 𝟘 × q PE.≡ 𝟘)) →
        Γ ⊢ t ∷ A →
        Γ »∙ A »∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
        Γ ⊢ u ∷ B [ t , rfl ]₁₀ →
        Γ ⊢ J″ d A t B u t rfl ≡ u ∷ B [ t , rfl ]₁₀
      J″-β-≡′ d ⊢t ⊢B ⊢u = subset*Term (J″-β-⇒* d ⊢t ⊢B ⊢u)

    opaque

      erase-J″ :
        (d : Dec (p PE.≡ 𝟘 × q PE.≡ 𝟘)) →
        erase′ b str (J″ d A t B u v w) PE.≡ erase′ b str u
      erase-J″ = λ where
        (yes _) → erase-Jᵉ
        (no _)  → PE.refl

opaque

  -- A translation that replaces every occurrence of []-cong with rfl
  -- and turns on equality reflection.

  replace-[]-cong-with-rfl : Configuration
  replace-[]-cong-with-rfl = λ where
      .preservation-of-reduction          → true
      .glassification                     → true
      .Configuration.TRₜ                  → TRₜ
      .Configuration.URₜ                  → URₜ
      .Opacity-allowed-→ ¬⊤               → ⊥-elim (¬⊤ _)
      .level-support-≤                    → refl-≤LS
      .unfolding-mode-≡                   → PE.refl
      .Unit-allowed-→                     → idᶠ
      .η-for-Unitʷ-≡                      → PE.refl
      .ΠΣ-allowed-→                       → idᶠ
      .K-allowed-→                        → idᶠ
      .Equality-reflection-→              → _
      .Emptyrec-allowed-→ _               → idᶠ
      .Unitrec-allowed-→ _                → idᶠ
      .Starˢ-sink-→                       → idᶠ
      .Prodrec-allowed-→ _                → idᶠ
      .natrec-mode-≡                      → PE.refl
      .Id-erased-⇔                        → id⇔
      .erased-matches-for-K-≡             → PE.refl
      .[]-cong′ _ _ _ _ _ _               → rfl
      .[]-cong′-[]                        → PE.refl
      .▸[]-cong′ _ _ _ _ _ _              → rflₘ
      .[]-cong′-cong ok l₁≡l₂ _ _ _ v₁≡v₂ →
        refl $
        []-cong-with-equality-reflection _ (TRₛ .[]-cong→Erased ok)
          (wf-⊢≡∷L l₁≡l₂ .proj₁) (wf-⊢≡∷ v₁≡v₂ .proj₂ .proj₁)
      .[]-cong′-subst _ ok ⊢l v⇒v′ →
        id $
        []-cong-with-equality-reflection _ (TRₛ .[]-cong→Erased ok) ⊢l
          (wf-⊢≡∷ (subsetTerm v⇒v′) .proj₂ .proj₁)
      .[]-cong′-β-≡′ ¬⊤ →
        ⊥-elim (¬⊤ _)
      .[]-cong′-β-⇒* _ ok ⊢l t≡t′ →
        id $
        []-cong-with-equality-reflection _ (TRₛ .[]-cong→Erased ok) ⊢l
          (rflⱼ′ t≡t′)
      .erase-[]-cong′ →
        PE.refl
      .J′                    → J
      .J′-[]                 → PE.refl
      .▸J′ _ _               → Jₘ-generalised
      .▸J′₀₁ ok              → J₀ₘ₁ (≡-not-none-preserved ok)
                                 PE.refl PE.refl
      .▸J′₀₂ ok              → J₀ₘ₂ (≡-not-none-preserved ok)
      .J′-cong               → J-cong′
      .J′-subst _ ⊢B ⊢u w⇒w′ → redMany (J-subst′ ⊢B ⊢u w⇒w′)
      .J′-β-≡′ ¬⊤            → ⊥-elim (¬⊤ _)
      .J′-β-⇒* _ t≡t′ ⊢B ⊢u  → redMany (J-β-⇒ t≡t′ ⊢B ⊢u)
      .erase-J′              → PE.refl
    where
    TRₜ : Type-restrictions
    TRₜ = with-equality-reflection (no-[]-cong-TR TRₛ)

    URₜ : Usage-restrictions
    URₜ = no-[]-cong-UR URₛ

    open Configuration hiding (TRₜ; URₜ)
    open Definition.Typed TRₜ
    open Definition.Typed.Properties TRₜ hiding ([]-cong′)
    open Definition.Typed.Well-formed TRₜ
    open Graded.Usage URₜ
    open Graded.Usage.Properties URₜ

opaque

  -- A translation that only turns on equality reflection, no changes
  -- are made to the terms.

  turn-on-equality-reflection : Configuration
  turn-on-equality-reflection = λ where
      .preservation-of-reduction   → true
      .glassification              → true
      .Configuration.TRₜ           → TRₜ
      .Configuration.URₜ           → URₛ
      .Opacity-allowed-→ ¬⊤        → ⊥-elim (¬⊤ _)
      .level-support-≤             → refl-≤LS
      .unfolding-mode-≡            → PE.refl
      .Unit-allowed-→              → idᶠ
      .η-for-Unitʷ-≡               → PE.refl
      .ΠΣ-allowed-→                → idᶠ
      .K-allowed-→                 → idᶠ
      .Equality-reflection-→       → _
      .Emptyrec-allowed-→ _        → idᶠ
      .Unitrec-allowed-→ _         → idᶠ
      .Starˢ-sink-→                → idᶠ
      .Prodrec-allowed-→ _         → idᶠ
      .natrec-mode-≡               → PE.refl
      .Id-erased-⇔                 → id⇔
      .erased-matches-for-K-≡      → PE.refl
      .[]-cong′                    → []-cong
      .[]-cong′-[]                 → PE.refl
      .▸[]-cong′ ok ▸l ▸A ▸t ▸u ▸v →
        []-congₘ ▸l ▸A ▸t ▸u ▸v ok
      .[]-cong′-cong ok l₁≡l₂ A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ →
        []-cong-cong l₁≡l₂ A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ ok
      .[]-cong′-subst _ ok ⊢l v⇒v′ → redMany ([]-cong-subst ⊢l v⇒v′ ok)
      .[]-cong′-β-≡′ ¬⊤            → ⊥-elim (¬⊤ _)
      .[]-cong′-β-⇒* _ ok ⊢l t≡t′  → redMany ([]-cong-β ⊢l t≡t′ ok)
      .erase-[]-cong′              → PE.refl
      .J′                          → J
      .J′-[]                       → PE.refl
      .▸J′                         → Jₘ
      .▸J′₀₁ ok                    → J₀ₘ₁ ok PE.refl PE.refl
      .▸J′₀₂                       → J₀ₘ₂
      .J′-cong                     → J-cong′
      .J′-subst _ ⊢B ⊢u w⇒w′       → redMany (J-subst′ ⊢B ⊢u w⇒w′)
      .J′-β-≡′ ¬⊤                  → ⊥-elim (¬⊤ _)
      .J′-β-⇒* _ t≡t′ ⊢B ⊢u        → redMany (J-β-⇒ t≡t′ ⊢B ⊢u)
      .erase-J′                    → PE.refl
    where
    TRₜ : Type-restrictions
    TRₜ = with-equality-reflection TRₛ

    open Configuration hiding (TRₜ; URₜ)
    open Definition.Typed TRₜ
    open Definition.Typed.Properties TRₜ hiding ([]-cong′)
    open Graded.Usage URₛ
