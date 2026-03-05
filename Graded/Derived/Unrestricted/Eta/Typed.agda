------------------------------------------------------------------------
-- Some properties related to typing and Unrestricted
------------------------------------------------------------------------

open import Graded.Modality
open import Definition.Typed.Restrictions

module Graded.Derived.Unrestricted.Eta.Typed
  {a} {M : Set a}
  {𝕄 : Modality M}
  (open Modality 𝕄)
  (R : Type-restrictions 𝕄)
  (open Type-restrictions R)
  -- Strong unit types are assumed to be allowed.
  (Unit-ok : Unitˢ-allowed)
  -- It is assumed that strong Σ-types are allowed for the quantities
  -- ω and ω.
  (Σˢ-ok : Σˢ-allowed ω ω)
  where

open import Definition.Typed R
open import Definition.Typed.Consequences.Inequality R
open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.EqRelInstance R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
  hiding ([]ⱼ; []-cong′; inversion-[])
open import Definition.Typed.Reasoning.Level R
open import Definition.Typed.Substitution R
open import Definition.Typed.Weakening R
open import Definition.Typed.Well-formed R

open import Definition.Untyped M hiding (_[_])
open import Definition.Untyped.Properties M
open import Definition.Untyped.Sup R
open import Graded.Derived.Unrestricted.Eta.Untyped 𝕄

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Sum

private variable
  Γ             : Cons _ _
  A A₁ A₂ B t u : Term _
  l l₁ l₂       : Lvl _

------------------------------------------------------------------------
-- Typing rules

opaque
  unfolding Unrestricted

  -- An equality rule for Unrestricted.

  Unrestricted-cong :
    Γ ⊢ l₁ ≡ l₂ ∷Level →
    Γ ⊢ A₁ ≡ A₂ →
    Γ ⊢ Unrestricted l₁ A₁ ≡ Unrestricted l₂ A₂
  Unrestricted-cong l₁≡l₂ A₁≡A₂ =
    let ⊢A₁ , _ = wf-⊢≡ A₁≡A₂ in
    ΠΣ-cong A₁≡A₂
      (Lift-cong (wkEqLevel₁ ⊢A₁ l₁≡l₂) (refl (⊢Unit (∙ ⊢A₁) Unit-ok)))
      Σˢ-ok

opaque
  unfolding Unrestricted

  -- A typing rule for Unrestricted.

  Unrestrictedⱼ : Γ ⊢ l ∷Level → Γ ⊢ A → Γ ⊢ Unrestricted l A
  Unrestrictedⱼ ⊢l ⊢A =
    wf-⊢≡ (Unrestricted-cong (refl-⊢≡∷L ⊢l) (refl ⊢A)) .proj₁

opaque
  unfolding Unrestricted

  -- An equality rule for Unrestricted.

  Unrestricted-cong-U :
    Γ ⊢ l₁ ≡ l₂ ∷Level →
    Γ ⊢ A₁ ≡ A₂ ∷ U l₁ →
    Γ ⊢ Unrestricted l₁ A₁ ≡ Unrestricted l₂ A₂ ∷ U l₁
  Unrestricted-cong-U l₁≡l₂ A₁≡A₂ =
    let _ , ⊢A₁ , _ = wf-⊢≡∷ A₁≡A₂
        ⊢A₁′        = univ ⊢A₁
        ⊢l₁         = inversion-U-Level (wf-⊢∷ ⊢A₁)
    in
    ΠΣ-cong′ A₁≡A₂
      (conv
         (Lift-cong′ (wkEqLevel₁ ⊢A₁′ l₁≡l₂)
            (refl (Unitⱼ (∙ ⊢A₁′) Unit-ok)))
         (U-cong-⊢≡ (supᵘₗ-zeroˡ (wkLevel₁ ⊢A₁′ ⊢l₁))))
      Σˢ-ok

opaque

  -- A typing rule for Unrestricted.

  Unrestrictedⱼ-U : Γ ⊢ A ∷ U l → Γ ⊢ Unrestricted l A ∷ U l
  Unrestrictedⱼ-U ⊢A∷U =
    let ⊢l = inversion-U-Level (wf-⊢∷ ⊢A∷U) in
    wf-⊢≡∷ (Unrestricted-cong-U (refl-⊢≡∷L ⊢l) (refl ⊢A∷U))
      .proj₂ .proj₁

opaque
  unfolding Unrestricted [_]

  -- An equality rule for [_].

  []-cong′ :
    Γ ⊢ l ∷Level → Γ ⊢ t ≡ u ∷ A →
    Γ ⊢ [ t ] ≡ [ u ] ∷ Unrestricted l A
  []-cong′ ⊢l t≡u =
    let ⊢A , _ = wf-⊢≡∷ t≡u in
    prod-cong (Liftⱼ (wkLevel₁ ⊢A ⊢l) (⊢Unit (∙ ⊢A) Unit-ok)) t≡u
      (refl $
       liftⱼ′ (PE.subst (_⊢_∷Level _) (PE.sym $ wk1-sgSubst _ _) ⊢l)
         (starⱼ (wf ⊢A) Unit-ok))
      Σˢ-ok

opaque

  -- A typing rule for [_].

  []ⱼ : Γ ⊢ l ∷Level → Γ ⊢ t ∷ A → Γ ⊢ [ t ] ∷ Unrestricted l A
  []ⱼ ⊢l ⊢t = wf-⊢≡∷ ([]-cong′ ⊢l (refl ⊢t)) .proj₂ .proj₁

opaque
  unfolding Unrestricted unbox

  -- An equality rule for unbox.

  unbox-cong : Γ ⊢ t ≡ u ∷ Unrestricted l A → Γ ⊢ unbox t ≡ unbox u ∷ A
  unbox-cong t≡u =
    let _ , ⊢Lift , _  = inversion-ΠΣ (wf-⊢≡∷ t≡u .proj₁)
        ⊢wk1-l , ⊢Unit = inversion-Lift ⊢Lift
    in
    fst-cong (Liftⱼ ⊢wk1-l ⊢Unit) t≡u

opaque

  -- A typing rule for unbox.

  unboxⱼ : Γ ⊢ t ∷ Unrestricted l A → Γ ⊢ unbox t ∷ A
  unboxⱼ ⊢t = wf-⊢≡∷ (unbox-cong (refl ⊢t)) .proj₂ .proj₁

opaque
  unfolding [_] unbox

  -- A β-rule for unbox.

  Unrestricted-β :
    Γ ⊢ t ∷ A →
    Γ ⊢ unbox [ t ] ≡ t ∷ A
  Unrestricted-β ⊢t =
    let ⊢Γ = wfTerm ⊢t
        ⊢A = wf-⊢∷ ⊢t
    in
    Σ-β₁-≡ (Liftⱼ (⊢zeroᵘ (∙ ⊢A)) (⊢Unit (∙ ⊢A) Unit-ok)) ⊢t
      (liftⱼ′ (⊢zeroᵘ ⊢Γ) (starⱼ ⊢Γ Unit-ok)) Σˢ-ok

opaque
  unfolding Unrestricted unbox

  -- An η-rule for Unrestricted.

  Unrestricted-η :
    Γ ⊢ t ∷ Unrestricted l A →
    Γ ⊢ u ∷ Unrestricted l A →
    Γ ⊢ unbox t ≡ unbox u ∷ A →
    Γ ⊢ t ≡ u ∷ Unrestricted l A
  Unrestricted-η {l} ⊢t ⊢u t≡u =
    let _ , ⊢Lift , _ = inversion-ΠΣ (wf-⊢∷ ⊢t)
        ⊢wk1-l , _    = inversion-Lift ⊢Lift
    in
    Σ-η′ ⊢t ⊢u t≡u $
    Lift-η′ (sndⱼ′ ⊢t)
      (_⊢_∷_.conv (sndⱼ′ ⊢u) $
       Lift-cong
         (PE.subst (_⊢_≡_∷Level _ _)
            (PE.trans (wk1-sgSubst l _) $
             PE.sym $ wk1-sgSubst _ _) $
          refl-⊢≡∷L (substLevel ⊢wk1-l (fstⱼ′ ⊢u)))
         (refl (⊢Unit (wfTerm ⊢t) Unit-ok))) $
    η-unit (lowerⱼ (sndⱼ′ ⊢t)) (lowerⱼ (sndⱼ′ ⊢u)) (inj₁ PE.refl)

opaque

  -- An instance of the η-rule.

  [unbox] :
    Γ ⊢ l ∷Level →
    Γ ⊢ t ∷ Unrestricted l A →
    Γ ⊢ [ unbox t ] ≡ t ∷ Unrestricted l A
  [unbox] ⊢l ⊢t =
    Unrestricted-η ([]ⱼ ⊢l (unboxⱼ ⊢t)) ⊢t $
    Unrestricted-β (unboxⱼ ⊢t)

------------------------------------------------------------------------
-- Inversion lemmas for typing

opaque
  unfolding Unrestricted

  -- An inversion lemma for Unrestricted.

  inversion-Unrestricted-∷ :
    Γ ⊢ Unrestricted l A ∷ B →
    ∃ λ l′ →
      Γ ⊢ A ∷ U l′ × (Γ ⊢ B ≡ U l′) × Γ »∙ A ⊢ wk1 l ∷Level ×
      (⦃ not-ok : No-equality-reflection ⦄ →
       Γ »∙ A ⊢ wk1 l′ ≡ wk1 l ∷Level)
  inversion-Unrestricted-∷ {l} ⊢Unrestricted =
    let l′ , ⊢l′ , ⊢A , ⊢Lift , B≡ , _ = inversion-ΠΣ-U ⊢Unrestricted
        l″ , ⊢wk1-l , ⊢Unit , U≡U₁     = inversion-Lift∷ ⊢Lift
        U≡U₂ , _                       = inversion-Unit-U ⊢Unit
    in
    _ , ⊢A , B≡ , ⊢wk1-l ,
    (wk1 l′              ≡⟨ U-injectivity ⦃ ok = included ⦄ U≡U₁ ⟩⊢
     l″ supᵘₗ wk1 l      ≡⟨ supᵘₗ-cong (U-injectivity ⦃ ok = included ⦄ U≡U₂)
                              (refl-⊢≡∷L ⊢wk1-l) ⟩⊢
     zeroᵘₗ supᵘₗ wk1 l  ≡⟨ supᵘₗ-zeroˡ ⊢wk1-l ⟩⊢∎
     wk1 l               ∎)

opaque
  unfolding Unrestricted

  -- Another inversion lemma for Unrestricted.

  inversion-Unrestricted :
    ⦃ ok : No-equality-reflection or-empty Γ .vars ⦄ →
    Γ ⊢ Unrestricted l A →
    (Γ ⊢ A) × Γ »∙ A ⊢ wk1 l ∷Level
  inversion-Unrestricted (ΠΣⱼ ⊢Lift _)        =
    let ⊢wk1-l , _ = inversion-Lift ⊢Lift in
    ⊢∙→⊢ (wf ⊢Lift) , ⊢wk1-l
  inversion-Unrestricted (univ ⊢Unrestricted) =
    let _ , ⊢A , _ , ⊢wk1-l , _ =
          inversion-Unrestricted-∷ ⊢Unrestricted
    in
    univ ⊢A , ⊢wk1-l

opaque
  unfolding [_]

  -- An inversion lemma for [_].

  inversion-[] :
    Γ ⊢ [ t ] ∷ A →
    ∃₄ λ B q C l →
       Γ ⊢ t ∷ B ×
       Γ ⊢ A ≡ Σˢ ω , q ▷ B ▹ C ×
       Γ ⊢ C [ t ]₀ ≡ Lift l Unitˢ
  inversion-[] ⊢[] =
    let B , C , q , _ , _ , ⊢t , ⊢lift , A≡ , _ = inversion-prod ⊢[]
        l , D , ⊢star , C[t]₀≡                  = inversion-lift ⊢lift
        D≡ , _                                  = inversion-star ⊢star
        _ , ⊢Lift                               = wf-⊢≡ C[t]₀≡
        ⊢l , _                                  = inversion-Lift ⊢Lift
    in
    B , q , C , l , ⊢t , A≡ , trans C[t]₀≡ (Lift-cong (refl-⊢≡∷L ⊢l) D≡)

opaque
  unfolding Unrestricted

  -- Another inversion lemma for [_].

  inversion-[]′ :
    ⦃ ok : No-equality-reflection or-empty Γ .vars ⦄ →
    Γ ⊢ [ t ] ∷ Unrestricted l A →
    Γ ⊢ t ∷ A × Γ »∙ A ⊢ wk1 l ∷Level
  inversion-[]′ ⊢[] =
    let _ , _ , _ , _ , ⊢t , Unrestricted≡ , _ = inversion-[] ⊢[]
        ⊢Unrestricted , _                      = wf-⊢≡ Unrestricted≡
        _ , ⊢wk1-l                             = inversion-Unrestricted
                                                   ⊢Unrestricted
        A≡ , _                                 = ΠΣ-injectivity
                                                   Unrestricted≡
    in
    conv ⊢t (sym A≡) , ⊢wk1-l

opaque
  unfolding [_]

  -- A certain form of inversion for [_] does not hold.

  ¬-inversion-[]′ :
    ¬ (∀ {n₁ n₂} {Γ : Cons n₁ n₂} {t A : Term n₂} →
       Γ ⊢ [ t ] ∷ A →
       ∃₃ λ B q l → Γ ⊢ t ∷ B × Γ ⊢ A ≡ Σˢ ω , q ▷ B ▹ Lift l Unitˢ)
  ¬-inversion-[]′ inversion-[] = bad
    where
    Γ′ : Con Term 0
    Γ′ = ε

    t′ A′ : Term 0
    t′ = zero
    A′ = Σˢ ω , ω ▷ ℕ ▹
         natrec 𝟙 𝟙 𝟙 U₀ (Lift zeroᵘₗ Unitˢ) ℕ (var x0)

    ⊢Γ′∙ℕ : ε »⊢ Γ′ ∙ ℕ
    ⊢Γ′∙ℕ = ∙ ⊢ℕ εε

    ⊢Γ′∙ℕ∙U : ε »⊢ Γ′ ∙ ℕ ∙ U₀
    ⊢Γ′∙ℕ∙U = ∙ ⊢U₀ ⊢Γ′∙ℕ

    ⊢Lift-Unit :
      ⊢ Γ → Γ ⊢ Lift zeroᵘₗ Unitˢ ∷ U₀
    ⊢Lift-Unit ⊢Γ =
      conv (Liftⱼ′ (⊢zeroᵘ ⊢Γ) (Unitⱼ ⊢Γ Unit-ok))
        (U-cong-⊢≡ (supᵘₗ-zeroˡ (⊢zeroᵘ ⊢Γ)))

    ⊢[t′] : ε » Γ′ ⊢ [ t′ ] ∷ A′
    ⊢[t′] = prodⱼ
      (_⊢_.univ $
       natrecⱼ (⊢Lift-Unit ⊢Γ′∙ℕ) (ℕⱼ (∙ ⊢U₀ (∙ ⊢ℕ ⊢Γ′∙ℕ)))
         (var ⊢Γ′∙ℕ here))
      (zeroⱼ εε)
      (conv (liftⱼ′ (⊢zeroᵘ εε) (starⱼ εε Unit-ok))
         (_⊢_≡_.sym $ _⊢_≡_.univ $
          natrec-zero (⊢Lift-Unit εε) (ℕⱼ ⊢Γ′∙ℕ∙U)))
      Σˢ-ok

    ℕ≡Lift : ∃ λ l → ε » Γ′ ⊢ ℕ ≡ Lift l Unitˢ
    ℕ≡Lift =
      case inversion-[] ⊢[t′] of
        λ (_ , _ , _ , _ , A′≡) →
      case ΠΣ-injectivity ⦃ ok = ε ⦄ A′≡ of
        λ (_ , ≡Lift , _ , _ , _) →
        _
      , _⊢_≡_.trans
          (_⊢_≡_.sym $ _⊢_≡_.univ $
           natrec-suc (⊢Lift-Unit εε) (ℕⱼ ⊢Γ′∙ℕ∙U) (zeroⱼ εε))
          (≡Lift (refl (sucⱼ (zeroⱼ εε))))

    bad : ⊥
    bad = Lift≢ℕ ⦃ ok = ε ⦄ (sym (ℕ≡Lift .proj₂))

opaque
  unfolding Unrestricted

  -- Another form of inversion for [] also does not hold.

  ¬-inversion-[] :
    ¬ (∀ {n₁ n₂} {Γ : Cons n₁ n₂} {t A : Term n₂} →
       Γ ⊢ [ t ] ∷ A →
       ∃₂ λ B l → Γ ⊢ t ∷ B × Γ ⊢ A ≡ Unrestricted l B)
  ¬-inversion-[] inversion-[] =
    ¬-inversion-[]′ λ ⊢[] →
    let B , l , ⊢t , A≡ = inversion-[] ⊢[] in
    B , ω , wk1 l , ⊢t , A≡

opaque
  unfolding unbox

  -- An inversion lemma for unbox.

  inversion-unbox :
    Γ ⊢ unbox t ∷ A →
    ∃₂ λ q B → Γ ⊢ t ∷ Σˢ ω , q ▷ A ▹ B
  inversion-unbox ⊢unbox =
    let _ , C , q , _ , ⊢C , ⊢t , A≡B = inversion-fst ⊢unbox in
    q , C , conv ⊢t (ΠΣ-cong (sym A≡B) (refl ⊢C) (⊢∷ΠΣ→ΠΣ-allowed ⊢t))

opaque
  unfolding unbox

  -- A certain form of inversion for unbox does not hold.

  ¬-inversion-unbox′ :
    ¬ (∀ {n₁ n₂} {Γ : Cons n₁ n₂} {t A : Term n₂} →
       Γ ⊢ unbox t ∷ A →
       ∃₂ λ q l → Γ ⊢ t ∷ Σˢ ω , q ▷ A ▹ Lift l Unitˢ)
  ¬-inversion-unbox′ inversion-unbox = bad
    where
    Γ′ : Con Term 0
    Γ′ = ε

    t′ A′ : Term 0
    t′ = prodˢ ω zero zero
    A′ = ℕ

    ⊢Γ′∙ℕ : ε »⊢ Γ′ ∙ ℕ
    ⊢Γ′∙ℕ = ∙ ⊢ℕ εε

    ⊢t′₁ : ε » Γ′ ⊢ t′ ∷ Σˢ ω , ω ▷ ℕ ▹ ℕ
    ⊢t′₁ = prodⱼ (⊢ℕ ⊢Γ′∙ℕ) (zeroⱼ εε) (zeroⱼ εε) Σˢ-ok

    ⊢unbox-t′ : ε » Γ′ ⊢ unbox t′ ∷ A′
    ⊢unbox-t′ = fstⱼ (⊢ℕ ⊢Γ′∙ℕ) ⊢t′₁

    unbox-t′≡zero : ε » Γ′ ⊢ unbox t′ ≡ zero ∷ A′
    unbox-t′≡zero =
      Σ-β₁ (⊢ℕ ⊢Γ′∙ℕ) (zeroⱼ εε) (zeroⱼ εε) PE.refl Σˢ-ok

    ⊢t′₂ : ∃₂ λ q l → ε » Γ′ ⊢ t′ ∷ Σˢ ω , q ▷ A′ ▹ Lift l Unitˢ
    ⊢t′₂ =
      let _ , _ , ⊢t′ = inversion-unbox ⊢unbox-t′ in
      _ , _ , ⊢t′

    ⊢snd-t′ : ∃ λ l → ε » Γ′ ⊢ snd ω t′ ∷ Lift l Unitˢ
    ⊢snd-t′ =
      let _ , _ , ⊢t′   = ⊢t′₂
          _ , ⊢Lift , _ = inversion-ΠΣ (wf-⊢∷ ⊢t′)
      in
      _ , sndⱼ ⊢Lift ⊢t′

    ℕ≡Lift : ∃ λ l → ε » Γ′ ⊢ ℕ ≡ Lift l Unitˢ
    ℕ≡Lift =
      let l , ⊢snd-t′                     = ⊢snd-t′
          _ , _ , _ , _ , _ , ⊢t′ , Unit≡ =
            inversion-snd ⊢snd-t′
          _ , _ , _ , _ , _ , ⊢zero , ⊢zero′ , Σ≡Σ , _ =
            inversion-prod ⊢t′
          F≡F′ , G≡G′ , _ , _ , _ = ΠΣ-injectivity ⦃ ok = ε ⦄ Σ≡Σ
          ≡ℕ                      = inversion-zero ⊢zero
          ≡ℕ′                     = inversion-zero ⊢zero′
      in
      l ,
      (_⊢_≡_.sym $
       trans Unit≡ $
       trans (G≡G′ (conv unbox-t′≡zero (_⊢_≡_.sym (trans F≡F′ ≡ℕ))))
       ≡ℕ′)

    bad : ⊥
    bad = Lift≢ℕ ⦃ ok = ε ⦄ (sym (ℕ≡Lift .proj₂))

opaque
  unfolding Unrestricted

  -- Another form of inversion for unbox also does not hold.

  ¬-inversion-unbox :
    ¬ (∀ {n₁ n₂} {Γ : Cons n₁ n₂} {t A : Term n₂} →
       Γ ⊢ unbox t ∷ A →
       ∃ λ l → Γ ⊢ t ∷ Unrestricted l A)
  ¬-inversion-unbox inversion-unbox =
    ¬-inversion-unbox′ λ ⊢unbox →
    let _ , ⊢t = inversion-unbox ⊢unbox in
    _ , _ , ⊢t
