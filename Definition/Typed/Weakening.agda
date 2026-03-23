------------------------------------------------------------------------
-- Typing and reduction are closed under weakenings
------------------------------------------------------------------------

{-# OPTIONS --backtracking-instance-search #-}

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Weakening
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped M as U hiding (wk; wk′)
open import Definition.Untyped.Allowed-literal R
open import Definition.Untyped.Erased 𝕄
open import Definition.Untyped.Inversion M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M
open import Definition.Untyped.Sup R
open import Definition.Untyped.Whnf M type-variant
open import Definition.Typed R
open import Definition.Typed.Inversion.Primitive R
open import Definition.Typed.Properties.Admissible.Level.Primitive R
open import Definition.Typed.Properties.Admissible.Var R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Size R

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
open import Tools.Size
open import Tools.Size.Instances
open import Tools.Sum as ⊎

private
  variable
    ∇ : DCon (Term 0) _
    k ℓ n n′ m : Nat
    s s₂ : Size
    A A′ A₁ A₂ B C t t′ t₁ t₂ u : Term n
    l l₁ l₂ : Lvl _
    Γ Δ Δ′ Η : Con Term _
    ρ ρ′ ρ₁ ρ₂ : Wk _ _
    𝓙 : Judgement _

------------------------------------------------------------------------
-- Some lemmas related to Allowed-literal

opaque
  unfolding Allowed-literal

  -- A weakening lemma for Allowed-literal.

  Allowed-literal-wk-⇔ :
    Allowed-literal (U.wk ρ l) ⇔ Allowed-literal l
  Allowed-literal-wk-⇔ {l = ωᵘ+ _}   = id⇔
  Allowed-literal-wk-⇔ {l = level _} =
    sym⇔ wk-Level-literal ×-cong-⇔ id⇔

opaque
  unfolding Allowed-literal→Universe-level Allowed-literal-wk-⇔

  Allowed-literal→Universe-level-Allowed-literal-wk-⇔ :
    {ok : Allowed-literal l} →
    Allowed-literal→Universe-level
      (Allowed-literal-wk-⇔ {ρ = ρ} .proj₂ ok) PE.≡
    Allowed-literal→Universe-level ok
  Allowed-literal→Universe-level-Allowed-literal-wk-⇔ {l = ωᵘ+ _} =
    PE.refl
  Allowed-literal→Universe-level-Allowed-literal-wk-⇔ {l = level _} =
    PE.cong 0ᵘ+ size-of-Level-wk-Level-literal

------------------------------------------------------------------------
-- The type _∷_⊇_

-- Weakening type

data _∷_⊇_ : Wk m n → Con Term m → Con Term n → Set a where
  id   :             id     ∷ Γ            ⊇ Γ
  step : ρ ∷ Δ ⊇ Γ → step ρ ∷ Δ ∙ A        ⊇ Γ
  lift : ρ ∷ Δ ⊇ Γ → lift ρ ∷ Δ ∙ U.wk ρ A ⊇ Γ ∙ A


-- Weakening composition

_•ₜ_ : ρ ∷ Γ ⊇ Δ → ρ′ ∷ Δ ⊇ Δ′ → ρ • ρ′ ∷ Γ ⊇ Δ′
id     •ₜ η′ = η′
step η •ₜ η′ = step (η •ₜ η′)
lift η •ₜ id = lift η
lift η •ₜ step η′ = step (η •ₜ η′)
_•ₜ_ {ρ = lift ρ} {ρ′ = lift ρ′} {Δ′ = Δ′ ∙ A} (lift η) (lift η′) =
  PE.subst (λ x → lift (ρ • ρ′) ∷ x ⊇ Δ′ ∙ A)
           (PE.cong₂ _∙_ PE.refl (PE.sym (wk-comp ρ ρ′ A)))
           (lift (η •ₜ η′))

-- Typed weakenings corresponding to the untyped weakenings returned
-- by wk₀.

wk₀∷⊇ : wk₀ ∷ Γ ⊇ ε
wk₀∷⊇ {Γ = ε}     = id
wk₀∷⊇ {Γ = _ ∙ _} = step wk₀∷⊇

opaque

  -- A weakening lemma for stepn.

  stepn∷⊇ : ρ ∷ drop k Δ ⊇ Γ → stepn ρ k ∷ Δ ⊇ Γ
  stepn∷⊇ {k = 0}                ρ∷ = ρ∷
  stepn∷⊇ {k = 1+ _} {Δ = _ ∙ _} ρ∷ = step (stepn∷⊇ ρ∷)

opaque

  -- The weakening stepn id k is a well-formed weakening from drop k Δ
  -- to Δ.

  ⊇-drop : stepn id k ∷ Δ ⊇ drop k Δ
  ⊇-drop = stepn∷⊇ id

opaque

  -- A weakening lemma for liftn.

  liftn∷⊇ : ρ ∷ Δ ⊇ drop k Γ → liftn ρ k ∷ Δ ∙[ k ][ Γ ][ ρ ]ʷ ⊇ Γ
  liftn∷⊇ {k = 0}                ρ∷ = ρ∷
  liftn∷⊇ {k = 1+ _} {Γ = _ ∙ _} ρ∷ = lift (liftn∷⊇ ρ∷)

------------------------------------------------------------------------
-- The type _∷ʷ_⊇_

opaque

  -- A combination of _∷_⊇_ and ⊢_.

  _»_∷ʷ_⊇_ : DCon (Term 0) n′ → Wk m n → Con Term m → Con Term n → Set a
  ∇ » ρ ∷ʷ Δ ⊇ Γ = ρ ∷ Δ ⊇ Γ × ∇ »⊢ Δ

opaque
  unfolding _»_∷ʷ_⊇_

  -- A "constructor" for _∷ʷ_⊇_.

  ∷⊇→∷ʷ⊇ : ρ ∷ Δ ⊇ Γ → ∇ »⊢ Δ → ∇ » ρ ∷ʷ Δ ⊇ Γ
  ∷⊇→∷ʷ⊇ = _,_

opaque
  unfolding _»_∷ʷ_⊇_

  -- The relation _∷ʷ_⊇_ is contained in _∷_⊇_.

  ∷ʷ⊇→∷⊇ : ∇ » ρ ∷ʷ Δ ⊇ Γ → ρ ∷ Δ ⊇ Γ
  ∷ʷ⊇→∷⊇ = proj₁

opaque
  unfolding _»_∷ʷ_⊇_

  -- If ρ is a well-formed weakening from Γ to Δ, then Δ is
  -- well-formed.

  wf-∷ʷ⊇ : ∇ » ρ ∷ʷ Δ ⊇ Γ → ∇ »⊢ Δ
  wf-∷ʷ⊇ = proj₂

opaque
  unfolding _»_∷ʷ_⊇_

  -- A "constructor" for _∷ʷ_⊇_.

  idʷ : ∇ »⊢ Γ → ∇ » id ∷ʷ Γ ⊇ Γ
  idʷ ⊢Γ = id , ⊢Γ

opaque
  unfolding _»_∷ʷ_⊇_

  -- A "constructor" for _∷ʷ_⊇_.

  stepʷ : ρ ∷ Δ ⊇ Γ → ∇ » Δ ⊢ A → ∇ » step ρ ∷ʷ Δ ∙ A ⊇ Γ
  stepʷ ρ⊇ ⊢A = step ρ⊇ , ∙ ⊢A

opaque
  unfolding _»_∷ʷ_⊇_

  -- A variant of stepʷ.

  stepʷʷ : ∇ » ρ ∷ʷ Δ ⊇ Γ → ∇ » Δ ⊢ A → ∇ » step ρ ∷ʷ Δ ∙ A ⊇ Γ
  stepʷʷ = stepʷ ∘→ ∷ʷ⊇→∷⊇

opaque
  unfolding _»_∷ʷ_⊇_

  -- A "constructor" for _∷ʷ_⊇_.

  stepnʷ : ρ ∷ drop k Δ ⊇ Γ → ∇ »⊢ Δ → ∇ » stepn ρ k ∷ʷ Δ ⊇ Γ
  stepnʷ ρ⊇ ⊢Δ = stepn∷⊇ ρ⊇ , ⊢Δ

opaque

  -- A variant of stepnʷ.

  stepnʷʷ : ∇ » ρ ∷ʷ drop k Δ ⊇ Γ → ∇ »⊢ Δ → ∇ » stepn ρ k ∷ʷ Δ ⊇ Γ
  stepnʷʷ = stepnʷ ∘→ ∷ʷ⊇→∷⊇

opaque
  unfolding _»_∷ʷ_⊇_

  -- A "constructor" for _∷ʷ_⊇_.

  liftʷ : ρ ∷ Δ ⊇ Γ → ∇ » Δ ⊢ U.wk ρ A → ∇ » lift ρ ∷ʷ Δ ∙ U.wk ρ A ⊇ Γ ∙ A
  liftʷ ρ⊇ ⊢A = lift ρ⊇ , ∙ ⊢A

opaque
  unfolding _»_∷ʷ_⊇_

  -- A variant of liftʷ.

  liftʷʷ : ∇ » ρ ∷ʷ Δ ⊇ Γ → ∇ » Δ ⊢ U.wk ρ A → ∇ » lift ρ ∷ʷ Δ ∙ U.wk ρ A ⊇ Γ ∙ A
  liftʷʷ = liftʷ ∘→ ∷ʷ⊇→∷⊇

opaque
  unfolding _»_∷ʷ_⊇_

  -- The composition of well-formed weakenings is well-formed.

  _•ₜʷ_ : ∇ » ρ₁ ∷ʷ Η ⊇ Δ → ∇ » ρ₂ ∷ʷ Δ ⊇ Γ → ∇ » ρ₁ • ρ₂ ∷ʷ Η ⊇ Γ
  (ρ₁⊇ , ⊢Η) •ₜʷ (ρ₂⊇ , _) = (ρ₁⊇ •ₜ ρ₂⊇) , ⊢Η

opaque
  unfolding _»_∷ʷ_⊇_

  -- If Γ is well-formed, then wk₀ is a well-formed weakening from ε
  -- to Γ.

  wk₀∷ʷ⊇ : ∇ »⊢ Γ → ∇ » wk₀ ∷ʷ Γ ⊇ ε
  wk₀∷ʷ⊇ ⊢Γ = wk₀∷⊇ , ⊢Γ

opaque
  unfolding _»_∷ʷ_⊇_

  -- If Δ is well-formed, then stepn id k is a well-formed weakening
  -- from drop k Δ to Δ.

  ʷ⊇-drop : ∇ »⊢ Δ → ∇ » stepn id k ∷ʷ Δ ⊇ drop k Δ
  ʷ⊇-drop ⊢Δ = ⊇-drop , ⊢Δ

------------------------------------------------------------------------
-- Weakening lemmas

-- Weakening for _∷_∈_.

wkIndex : ∀ {n} → ρ ∷ Δ ⊇ Γ →
        let ρA = U.wk ρ A
            ρn = wkVar ρ n
        in  n ∷ A ∈ Γ → ρn ∷ ρA ∈ Δ
wkIndex id i = PE.subst (λ x → _ ∷ x ∈ _) (PE.sym (wk-id _)) i
wkIndex (step ρ) i = PE.subst (λ x → _ ∷ x ∈ _)
                              (wk1-wk _ _)
                              (there (wkIndex ρ i))
wkIndex (lift ρ) (there i) = PE.subst (λ x → _ ∷ x ∈ _)
                                      (wk1-wk≡lift-wk1 _ _)
                                      (there (wkIndex ρ i))
wkIndex (lift ρ) here =
  let G = _
      n = _
  in  PE.subst (λ x → n ∷ x ∈ G)
               (wk1-wk≡lift-wk1 _ _)
               here

private

  -- Below several properties are proved simultaneously using
  -- well-founded induction. The properties are collected in the
  -- record type P.

  record P (s : Size) : Set a where
    no-eta-equality
    field
      wk :
        ρ ∷ Δ ⊇ Γ → ∇ »⊢ Δ →
        (⊢A : ∇ » Γ ⊢ A) →
        size ⊢A PE.≡ s →
        ∇ » Δ ⊢ U.wk ρ A
      wkTerm :
        ρ ∷ Δ ⊇ Γ → ∇ »⊢ Δ →
        (⊢t : ∇ » Γ ⊢ t ∷ A) →
        size ⊢t PE.≡ s →
        ∇ » Δ ⊢ U.wk ρ t ∷ U.wk ρ A
      wkLevel :
        ρ ∷ Δ ⊇ Γ → ∇ »⊢ Δ →
        (⊢l : ∇ » Γ ⊢ l ∷Level) →
        size ⊢l PE.≡ s →
        ∇ » Δ ⊢ U.wk ρ l ∷Level
      wkEq :
        ρ ∷ Δ ⊇ Γ → ∇ »⊢ Δ →
        (A≡B : ∇ » Γ ⊢ A ≡ B) →
        size A≡B PE.≡ s →
        ∇ » Δ ⊢ U.wk ρ A ≡ U.wk ρ B
      wkEqTerm :
        ρ ∷ Δ ⊇ Γ → ∇ »⊢ Δ →
        (t≡u : ∇ » Γ ⊢ t ≡ u ∷ A) →
        size t≡u PE.≡ s →
        ∇ » Δ ⊢ U.wk ρ t ≡ U.wk ρ u ∷ U.wk ρ A
      wkEqLevel :
        ρ ∷ Δ ⊇ Γ → ∇ »⊢ Δ →
        (l₁≡l₂ : ∇ » Γ ⊢ l₁ ≡ l₂ ∷Level) →
        size l₁≡l₂ PE.≡ s →
        ∇ » Δ ⊢ U.wk ρ l₁ ≡ U.wk ρ l₂ ∷Level

-- Variants of the fields of P.

private module Variants (hyp : ∀ {s₁} → s₁ <ˢ s₂ → P s₁) where

  opaque

    -- Variants of the fields of P.

    wk :
      ρ ∷ Δ ⊇ Γ → ∇ »⊢ Δ →
      (⊢A : ∇ » Γ ⊢ A)
      ⦃ lt : size ⊢A <ˢ s₂ ⦄ →
      ∇ » Δ ⊢ U.wk ρ A
    wk ρ⊇ ⊢Δ ⊢A ⦃ lt ⦄ = P.wk (hyp lt) ρ⊇ ⊢Δ ⊢A PE.refl

    wkTerm :
      ρ ∷ Δ ⊇ Γ → ∇ »⊢ Δ →
      (⊢t : ∇ » Γ ⊢ t ∷ A)
      ⦃ lt : size ⊢t <ˢ s₂ ⦄ →
      ∇ » Δ ⊢ U.wk ρ t ∷ U.wk ρ A
    wkTerm ρ⊇ ⊢Δ ⊢t ⦃ lt ⦄ = P.wkTerm (hyp lt) ρ⊇ ⊢Δ ⊢t PE.refl

    wkLevel :
      ρ ∷ Δ ⊇ Γ → ∇ »⊢ Δ →
      (⊢l : ∇ » Γ ⊢ l ∷Level) →
      ⦃ lt : size ⊢l <ˢ s₂ ⦄ →
      ∇ » Δ ⊢ U.wk ρ l ∷Level
    wkLevel ρ⊇ ⊢Δ ⊢l ⦃ lt ⦄ = P.wkLevel (hyp lt) ρ⊇ ⊢Δ ⊢l PE.refl

    wkEq :
      ρ ∷ Δ ⊇ Γ → ∇ »⊢ Δ →
      (A≡B : ∇ » Γ ⊢ A ≡ B)
      ⦃ lt : size A≡B <ˢ s₂ ⦄ →
      ∇ » Δ ⊢ U.wk ρ A ≡ U.wk ρ B
    wkEq ρ⊇ ⊢Δ A≡B ⦃ lt ⦄ = P.wkEq (hyp lt) ρ⊇ ⊢Δ A≡B PE.refl

    wkEqTerm :
      ρ ∷ Δ ⊇ Γ → ∇ »⊢ Δ →
      (t≡u : ∇ » Γ ⊢ t ≡ u ∷ A)
      ⦃ lt : size t≡u <ˢ s₂ ⦄ →
      ∇ » Δ ⊢ U.wk ρ t ≡ U.wk ρ u ∷ U.wk ρ A
    wkEqTerm ρ⊇ ⊢Δ t≡u ⦃ lt ⦄ = P.wkEqTerm (hyp lt) ρ⊇ ⊢Δ t≡u PE.refl

    wkEqLevel :
      ρ ∷ Δ ⊇ Γ → ∇ »⊢ Δ →
      (l₁≡l₂ : ∇ » Γ ⊢ l₁ ≡ l₂ ∷Level) →
      ⦃ lt : size l₁≡l₂ <ˢ s₂ ⦄ →
      ∇ » Δ ⊢ U.wk ρ l₁ ≡ U.wk ρ l₂ ∷Level
    wkEqLevel ρ⊇ ⊢Δ l₁≡l₂ ⦃ lt ⦄ =
      P.wkEqLevel (hyp lt) ρ⊇ ⊢Δ l₁≡l₂ PE.refl

-- The type P s is inhabited for every s.

private module Inhabited where

  opaque
    unfolding size

    -- A weakening lemma for _⊢_.

    wk′ :
      (∀ {s₁} → s₁ <ˢ s₂ → P s₁) →
      ρ ∷ Δ ⊇ Γ → ∇ »⊢ Δ →
      (⊢A : ∇ » Γ ⊢ A) →
      size ⊢A PE.≡ s₂ →
      ∇ » Δ ⊢ U.wk ρ A
    wk′ hyp ρ⊇ ⊢Δ = λ where
        (Levelⱼ ok _) _ →
          Levelⱼ ok ⊢Δ
        (univ ⊢A) PE.refl →
          univ (wkTerm ρ⊇ ⊢Δ ⊢A)
        (Liftⱼ ⊢l ⊢A) PE.refl →
          Liftⱼ (wkLevel ρ⊇ ⊢Δ ⊢l) (wk ρ⊇ ⊢Δ ⊢A)
        (ΠΣⱼ ⊢B ok) PE.refl →
          let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢B
              ⊢A′           = wk ρ⊇ ⊢Δ ⊢A ⦃ lt = <ˢ-trans A< ! ⦄
          in
          ΠΣⱼ (wk (lift ρ⊇) (∙ ⊢A′) ⊢B) ok
        (Idⱼ ⊢A ⊢t ⊢u) PE.refl →
          Idⱼ (wk ρ⊇ ⊢Δ ⊢A) (wkTerm ρ⊇ ⊢Δ ⊢t) (wkTerm ρ⊇ ⊢Δ ⊢u)
      where
      open Variants hyp

  opaque
    unfolding size

    -- A weakening lemma for _⊢_∷_.

    wkTerm′ :
      (∀ {s₁} → s₁ <ˢ s₂ → P s₁) →
      ρ ∷ Δ ⊇ Γ → ∇ »⊢ Δ →
      (⊢t : ∇ » Γ ⊢ t ∷ A) →
      size ⊢t PE.≡ s₂ →
      ∇ » Δ ⊢ U.wk ρ t ∷ U.wk ρ A
    wkTerm′ hyp ρ⊇ ⊢Δ = λ where
        (conv ⊢t B≡A) PE.refl →
          conv (wkTerm ρ⊇ ⊢Δ ⊢t) (wkEq ρ⊇ ⊢Δ B≡A)
        (var _ x∈) _ →
          var ⊢Δ (wkIndex ρ⊇ x∈)
        (defn ⊢Γ α↦t PE.refl) PE.refl →
          defn ⊢Δ α↦t (wk₀-comp _ _)
        (Levelⱼ _ ok) _ →
          Levelⱼ ⊢Δ ok
        (zeroᵘⱼ ok _) _ →
          zeroᵘⱼ ok ⊢Δ
        (sucᵘⱼ ⊢t) PE.refl →
          sucᵘⱼ (wkTerm ρ⊇ ⊢Δ ⊢t)
        (supᵘⱼ ⊢t ⊢u) PE.refl →
          supᵘⱼ (wkTerm ρ⊇ ⊢Δ ⊢t) (wkTerm ρ⊇ ⊢Δ ⊢u)
        (Uⱼ l) PE.refl →
          PE.subst (_⊢_∷_ _ _) (PE.cong U $ PE.sym wk-1ᵘ+) $
          Uⱼ (wkLevel ρ⊇ ⊢Δ l)
        (Liftⱼ ⊢l₁ ⊢l₂ ⊢A) PE.refl →
          PE.subst (_⊢_∷_ _ _) (PE.cong U $ PE.sym wk-supᵘₗ) $
          Liftⱼ (wkLevel ρ⊇ ⊢Δ ⊢l₁) (wkLevel ρ⊇ ⊢Δ ⊢l₂)
            (wkTerm ρ⊇ ⊢Δ ⊢A)
        (liftⱼ ⊢l₂ ⊢A ⊢t) PE.refl →
          liftⱼ (wkLevel ρ⊇ ⊢Δ ⊢l₂) (wk ρ⊇ ⊢Δ ⊢A) (wkTerm ρ⊇ ⊢Δ ⊢t)
        (lowerⱼ ⊢t) PE.refl →
          lowerⱼ (wkTerm ρ⊇ ⊢Δ ⊢t)
        (ΠΣⱼ l ⊢A ⊢B ok) PE.refl →
          let ⊢A′ = wkTerm ρ⊇ ⊢Δ ⊢A in
          ΠΣⱼ (wkLevel ρ⊇ ⊢Δ l) ⊢A′
            (PE.subst (λ x → _ ⊢ _ ∷ U x)
              (PE.sym $ wk1-wk≡lift-wk1 _ _)
              (wkTerm (lift ρ⊇) (∙ univ ⊢A′) ⊢B))
            ok
        (lamⱼ ⊢B ⊢t ok) PE.refl →
          let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢t
              ⊢A′           = wk ρ⊇ ⊢Δ ⊢A ⦃ lt = <ˢ-trans A< ! ⦄
          in
          lamⱼ (wk (lift ρ⊇) (∙ ⊢A′) ⊢B) (wkTerm (lift ρ⊇) (∙ ⊢A′) ⊢t)
            ok
        (_∘ⱼ_ {G = B} ⊢t ⊢u) PE.refl →
          PE.subst (_⊢_∷_ _ _) (PE.sym $ wk-β B)
            (wkTerm ρ⊇ ⊢Δ ⊢t ∘ⱼ wkTerm ρ⊇ ⊢Δ ⊢u)
        (prodⱼ {G = B} ⊢B ⊢t ⊢u ok) PE.refl →
          let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢B
              ⊢A′           = wk ρ⊇ ⊢Δ ⊢A ⦃ lt = <ˢ-trans A< ! ⦄
          in
          prodⱼ (wk (lift ρ⊇) (∙ ⊢A′) ⊢B)
            (wkTerm ρ⊇ ⊢Δ ⊢t)
            (PE.subst (_⊢_∷_ _ _) (wk-β B) $
             wkTerm ρ⊇ ⊢Δ ⊢u)
            ok
        (fstⱼ ⊢B ⊢t) PE.refl →
          let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢B
              ⊢A′           = wk ρ⊇ ⊢Δ ⊢A ⦃ lt = <ˢ-trans A< ! ⦄
          in
          fstⱼ (wk (lift ρ⊇) (∙ ⊢A′) ⊢B) (wkTerm ρ⊇ ⊢Δ ⊢t)
        (sndⱼ {G = B} ⊢B ⊢t) PE.refl →
          let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢B
              ⊢A′           = wk ρ⊇ ⊢Δ ⊢A ⦃ lt = <ˢ-trans A< ! ⦄
          in
          PE.subst (_⊢_∷_ _ _) (PE.sym $ wk-β B) $
          sndⱼ (wk (lift ρ⊇) (∙ ⊢A′) ⊢B) (wkTerm ρ⊇ ⊢Δ ⊢t)
        (prodrecⱼ {A = C} ⊢C ⊢t ⊢u ok) PE.refl →
          let _ , (⊢A , A<) , (⊢B , B<) = ∙∙⊢→⊢-<ˢ ⊢u
              ⊢A′                       = wk ρ⊇ ⊢Δ ⊢A
                                            ⦃ lt = <ˢ-trans A< ! ⦄
              ⊢B′                       = wk (lift ρ⊇) (∙ ⊢A′) ⊢B
                                            ⦃ lt = <ˢ-trans B< ! ⦄
          in
          PE.subst (_⊢_∷_ _ _) (PE.sym $ wk-β C) $
          prodrecⱼ
            (wk (lift ρ⊇) (∙ ΠΣⱼ ⊢B′ ok) ⊢C)
            (wkTerm ρ⊇ ⊢Δ ⊢t)
            (PE.subst (_⊢_∷_ _ _) (wk-β-prodrec _ C) $
             wkTerm (lift (lift ρ⊇)) (∙ ⊢B′) ⊢u)
            ok
        (Emptyⱼ _) _ →
          Emptyⱼ ⊢Δ
        (emptyrecⱼ ⊢A ⊢t) PE.refl →
          emptyrecⱼ (wk ρ⊇ ⊢Δ ⊢A) (wkTerm ρ⊇ ⊢Δ ⊢t)
        (starⱼ ⊢Γ ok) PE.refl →
          starⱼ ⊢Δ ok
        (unitrecⱼ {A} ⊢A ⊢t ⊢u ok) PE.refl →
          PE.subst (_⊢_∷_ _ _) (PE.sym $ wk-β A) $
          unitrecⱼ (wk (lift ρ⊇) (∙ univ (Unitⱼ ⊢Δ ok)) ⊢A)
            (wkTerm ρ⊇ ⊢Δ ⊢t)
            (PE.subst (_⊢_∷_ _ _) (wk-β A) $
             wkTerm ρ⊇ ⊢Δ ⊢u)
            ok
        (Unitⱼ _ ok) PE.refl →
          Unitⱼ ⊢Δ ok
        (ℕⱼ _) _ →
          ℕⱼ ⊢Δ
        (zeroⱼ _) _ →
          zeroⱼ ⊢Δ
        (sucⱼ ⊢t) PE.refl →
          sucⱼ (wkTerm ρ⊇ ⊢Δ ⊢t)
        (natrecⱼ {A} ⊢t ⊢u ⊢v) PE.refl →
          let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢u
              ⊢A′           = wk (lift ρ⊇) (∙ univ (ℕⱼ ⊢Δ)) ⊢A
                                ⦃ lt = <ˢ-trans A< ! ⦄
          in
          PE.subst (_⊢_∷_ _ _) (PE.sym $ wk-β A) $
          natrecⱼ
            (PE.subst (_⊢_∷_ _ _) (wk-β A) $
             wkTerm ρ⊇ ⊢Δ ⊢t)
            (PE.subst (_⊢_∷_ _ _) (wk-β-natrec _ A) $
             wkTerm (lift (lift ρ⊇)) (∙ ⊢A′) ⊢u)
            (wkTerm ρ⊇ ⊢Δ ⊢v)
        (Idⱼ ⊢A ⊢t ⊢u) PE.refl →
          Idⱼ (wkTerm ρ⊇ ⊢Δ ⊢A) (wkTerm ρ⊇ ⊢Δ ⊢t) (wkTerm ρ⊇ ⊢Δ ⊢u)
        (rflⱼ ⊢t) PE.refl →
          rflⱼ (wkTerm ρ⊇ ⊢Δ ⊢t)
        (Jⱼ {B} ⊢t ⊢B ⊢u ⊢v ⊢w) PE.refl →
          let _ , (⊢A , A<) , _ = ∙∙⊢→⊢-<ˢ ⊢B
              ⊢A′               = wk ρ⊇ ⊢Δ ⊢A ⦃ lt = <ˢ-trans A< ! ⦄
          in
          PE.subst (_⊢_∷_ _ _) (PE.sym $ wk-β-doubleSubst _ B _ _) $
          Jⱼ (wkTerm ρ⊇ ⊢Δ ⊢t)
            (PE.subst₂ (λ A t → _ » _ ∙ U.wk _ _ ∙ Id A t _ ⊢ _)
               (PE.sym $ wk1-wk≡lift-wk1 _ _)
               (PE.sym $ wk1-wk≡lift-wk1 _ _) $
             wk (lift (lift ρ⊇))
               (∙ (Idⱼ
                     (PE.subst (_⊢_ _) (PE.sym $ lift-wk1 _ _) $
                      wk (step ρ⊇) (∙ ⊢A′) ⊢A ⦃ lt = <ˢ-trans A< ! ⦄)
                     (PE.subst₂ (_⊢_∷_ _)
                        (PE.sym $ lift-wk1 _ _)
                        (PE.sym $ lift-wk1 _ _) $
                      wkTerm (step ρ⊇) (∙ ⊢A′) ⊢t)
                     (PE.subst (_⊢_∷_ _ _) (wk1-wk≡lift-wk1 _ _) $
                      var₀ ⊢A′)))
               ⊢B)
            (PE.subst (_⊢_∷_ _ _) (wk-β-doubleSubst _ B _ _) $
             wkTerm ρ⊇ ⊢Δ ⊢u)
            (wkTerm ρ⊇ ⊢Δ ⊢v) (wkTerm ρ⊇ ⊢Δ ⊢w)
        (Kⱼ {B} ⊢B ⊢u ⊢v ok) PE.refl →
          let _ , ⊢Id                   = ∙⊢→⊢-<ˢ ⊢B
              (⊢A , A<) , (⊢t , t<) , _ = inversion-Id-⊢-<ˢ ⊢Id
              ⊢A′                       = wk ρ⊇ ⊢Δ ⊢A
                                            ⦃ lt = <ˢ-trans A< ! ⦄
              ⊢t′                       = wkTerm ρ⊇ ⊢Δ ⊢t
                                            ⦃ lt = <ˢ-trans t< ! ⦄
          in
          PE.subst (_⊢_∷_ _ _) (PE.sym $ wk-β B) $
          Kⱼ (wk (lift ρ⊇) (∙ Idⱼ ⊢A′ ⊢t′ ⊢t′) ⊢B)
            (PE.subst (_⊢_∷_ _ _) (wk-β B) $
             wkTerm ρ⊇ ⊢Δ ⊢u)
            (wkTerm ρ⊇ ⊢Δ ⊢v) ok
        ([]-congⱼ ⊢l ⊢A ⊢t ⊢u ⊢v ok) PE.refl →
          PE.subst (_⊢_∷_ _ _) (wk-Id-Erased _) $
          []-congⱼ (wkLevel ρ⊇ ⊢Δ ⊢l) (wk ρ⊇ ⊢Δ ⊢A)
            (wkTerm ρ⊇ ⊢Δ ⊢t) (wkTerm ρ⊇ ⊢Δ ⊢u) (wkTerm ρ⊇ ⊢Δ ⊢v) ok
      where
      open Variants hyp

  opaque
    unfolding size

    -- A weakening lemma for _⊢_∷_.

    wkLevel′ :
      (∀ {s₁} → s₁ <ˢ s₂ → P s₁) →
      ρ ∷ Δ ⊇ Γ → ∇ »⊢ Δ →
      (⊢l : ∇ » Γ ⊢ l ∷Level) →
      size ⊢l PE.≡ s₂ →
      ∇ » Δ ⊢ U.wk ρ l ∷Level
    wkLevel′ hyp ρ⊇ ⊢Δ = λ where
        (term ok ⊢l)   PE.refl → term ok (wkTerm ρ⊇ ⊢Δ ⊢l)
        (literal ok _) _       →
          literal (Allowed-literal-wk-⇔ .proj₂ ok) ⊢Δ
      where
      open Variants hyp

  opaque
    unfolding size

    -- A weakening lemma for _⊢_≡_.

    wkEq′ :
      (∀ {s₁} → s₁ <ˢ s₂ → P s₁) →
      ρ ∷ Δ ⊇ Γ → ∇ »⊢ Δ →
      (A₁≡A₂ : ∇ » Γ ⊢ A₁ ≡ A₂) →
      size A₁≡A₂ PE.≡ s₂ →
      ∇ » Δ ⊢ U.wk ρ A₁ ≡ U.wk ρ A₂
    wkEq′ hyp ρ⊇ ⊢Δ = λ where
        (univ A₁≡A₂) PE.refl →
          univ (wkEqTerm ρ⊇ ⊢Δ A₁≡A₂)
        (refl ⊢A) PE.refl →
          refl (wk ρ⊇ ⊢Δ ⊢A)
        (sym A₂≡A₁) PE.refl →
          sym (wkEq ρ⊇ ⊢Δ A₂≡A₁)
        (trans A₁≡A₂ A₂≡A₃) PE.refl →
          trans (wkEq ρ⊇ ⊢Δ A₁≡A₂) (wkEq ρ⊇ ⊢Δ A₂≡A₃)
        (U-cong l₁≡l₂) PE.refl →
          U-cong (wkEqTerm ρ⊇ ⊢Δ l₁≡l₂)
        (Lift-cong l₁≡l₂ A≡B) PE.refl →
          Lift-cong (wkEqLevel ρ⊇ ⊢Δ l₁≡l₂) (wkEq ρ⊇ ⊢Δ A≡B)
        (ΠΣ-cong A₁≡A₂ B₁≡B₂ ok) PE.refl →
          let _ , (⊢A₁ , A₁<) = ∙⊢→⊢-<ˢ B₁≡B₂
              ⊢A₁′            = wk ρ⊇ ⊢Δ ⊢A₁ ⦃ lt = <ˢ-trans A₁< ! ⦄
          in
          ΠΣ-cong (wkEq ρ⊇ ⊢Δ A₁≡A₂) (wkEq (lift ρ⊇) (∙ ⊢A₁′) B₁≡B₂) ok
        (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) PE.refl →
          Id-cong (wkEq ρ⊇ ⊢Δ A₁≡A₂) (wkEqTerm ρ⊇ ⊢Δ t₁≡t₂)
            (wkEqTerm ρ⊇ ⊢Δ u₁≡u₂)
      where
      open Variants hyp

  opaque
    unfolding size

    -- A weakening lemma for _⊢_≡_∷_.

    wkEqTerm′ :
      (∀ {s₁} → s₁ <ˢ s₂ → P s₁) →
      ρ ∷ Δ ⊇ Γ → ∇ »⊢ Δ →
      (t₁≡t₂ : ∇ » Γ ⊢ t₁ ≡ t₂ ∷ A) →
      size t₁≡t₂ PE.≡ s₂ →
      ∇ » Δ ⊢ U.wk ρ t₁ ≡ U.wk ρ t₂ ∷ U.wk ρ A
    wkEqTerm′ hyp ρ⊇ ⊢Δ = λ where
        (refl ⊢t) PE.refl →
          refl (wkTerm ρ⊇ ⊢Δ ⊢t)
        (sym ⊢A t₂≡t₁) PE.refl →
          sym (wk ρ⊇ ⊢Δ ⊢A) (wkEqTerm ρ⊇ ⊢Δ t₂≡t₁)
        (trans t₁≡t₂ t₂≡t₃) PE.refl →
          trans (wkEqTerm ρ⊇ ⊢Δ t₁≡t₂) (wkEqTerm ρ⊇ ⊢Δ t₂≡t₃)
        (conv t₁≡t₂ B≡A) PE.refl →
          conv (wkEqTerm ρ⊇ ⊢Δ t₁≡t₂) (wkEq ρ⊇ ⊢Δ B≡A)
        (δ-red ⊢Γ α↦t PE.refl PE.refl) PE.refl →
          δ-red ⊢Δ α↦t (wk₀-comp _ _) (wk₀-comp _ _)
        (sucᵘ-cong t₁≡t₂) PE.refl →
          sucᵘ-cong (wkEqTerm ρ⊇ ⊢Δ t₁≡t₂)
        (supᵘ-cong t₁≡t₂ u₁≡u₂) PE.refl →
          supᵘ-cong (wkEqTerm ρ⊇ ⊢Δ t₁≡t₂) (wkEqTerm ρ⊇ ⊢Δ u₁≡u₂)
        (supᵘ-zeroˡ l) PE.refl →
          supᵘ-zeroˡ (wkTerm ρ⊇ ⊢Δ l)
        (supᵘ-sucᵘ l₁ l₂) PE.refl →
          supᵘ-sucᵘ (wkTerm ρ⊇ ⊢Δ l₁) (wkTerm ρ⊇ ⊢Δ l₂)
        (supᵘ-assoc l₁ l₂ l₃) PE.refl →
          supᵘ-assoc (wkTerm ρ⊇ ⊢Δ l₁) (wkTerm ρ⊇ ⊢Δ l₂) (wkTerm ρ⊇ ⊢Δ l₃)
        (supᵘ-comm l₁ l₂) PE.refl →
          supᵘ-comm (wkTerm ρ⊇ ⊢Δ l₁) (wkTerm ρ⊇ ⊢Δ l₂)
        (supᵘ-idem ⊢l) PE.refl →
          supᵘ-idem (wkTerm ρ⊇ ⊢Δ ⊢l)
        (supᵘ-sub ⊢l) PE.refl →
          supᵘ-sub (wkTerm ρ⊇ ⊢Δ ⊢l)
        (U-cong l₁≡l₂) PE.refl →
          U-cong (wkEqTerm ρ⊇ ⊢Δ l₁≡l₂)
        (Lift-cong ⊢l₁ ⊢l₂ l₂≡l₂′ A≡B) PE.refl →
          PE.subst (_⊢_≡_∷_ _ _ _) (PE.cong U $ PE.sym wk-supᵘₗ) $
          Lift-cong (wkLevel ρ⊇ ⊢Δ ⊢l₁) (wkLevel ρ⊇ ⊢Δ ⊢l₂)
            (wkEqLevel ρ⊇ ⊢Δ l₂≡l₂′) (wkEqTerm ρ⊇ ⊢Δ A≡B)
        (lower-cong t≡u) PE.refl →
          lower-cong (wkEqTerm ρ⊇ ⊢Δ t≡u)
        (Lift-β ⊢A ⊢t) PE.refl →
          Lift-β (wk ρ⊇ ⊢Δ ⊢A) (wkTerm ρ⊇ ⊢Δ ⊢t)
        (Lift-η ⊢l₂ ⊢A ⊢t ⊢u t≡u) PE.refl →
          Lift-η (wkLevel ρ⊇ ⊢Δ ⊢l₂) (wk ρ⊇ ⊢Δ ⊢A) (wkTerm ρ⊇ ⊢Δ ⊢t)
            (wkTerm ρ⊇ ⊢Δ ⊢u) (wkEqTerm ρ⊇ ⊢Δ t≡u)
        (ΠΣ-cong ⊢l A₁≡A₂ B₁≡B₂ ok) PE.refl →
          let _ , (⊢A₁ , A₁<) = ∙⊢→⊢-<ˢ B₁≡B₂
              ⊢A₁′            = wk ρ⊇ ⊢Δ ⊢A₁ ⦃ lt = <ˢ-trans A₁< ! ⦄
          in
          ΠΣ-cong (wkLevel ρ⊇ ⊢Δ ⊢l) (wkEqTerm ρ⊇ ⊢Δ A₁≡A₂)
            (PE.subst (λ x → _ ⊢ _ ≡ _ ∷ U x)
              (PE.sym $ wk1-wk≡lift-wk1 _ _)
              (wkEqTerm (lift ρ⊇) (∙ ⊢A₁′) B₁≡B₂))
            ok
        (app-cong {G = B} t₁≡t₂ u₁≡u₂) PE.refl →
          PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ wk-β B) $
          app-cong (wkEqTerm ρ⊇ ⊢Δ t₁≡t₂) (wkEqTerm ρ⊇ ⊢Δ u₁≡u₂)
        (β-red {B} {t} ⊢B ⊢t ⊢u eq ok) PE.refl →
          let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢B
              ⊢A′           = wk ρ⊇ ⊢Δ ⊢A ⦃ lt = <ˢ-trans A< ! ⦄
          in
          PE.subst₂ (_⊢_≡_∷_ _ _) (PE.sym $ wk-β t) (PE.sym $ wk-β B) $
          β-red (wk (lift ρ⊇) (∙ ⊢A′) ⊢B) (wkTerm (lift ρ⊇) (∙ ⊢A′) ⊢t)
            (wkTerm ρ⊇ ⊢Δ ⊢u) eq ok
        (η-eq {f = t₁} {g = t₂} ⊢B ⊢t₁ ⊢t₂ t₁0≡t₂0 ok) PE.refl →
          let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ t₁0≡t₂0
              ⊢A′           = wk ρ⊇ ⊢Δ ⊢A ⦃ lt = <ˢ-trans A< ! ⦄
          in
          η-eq (wk (lift ρ⊇) (∙ ⊢A′) ⊢B) (wkTerm ρ⊇ ⊢Δ ⊢t₁)
            (wkTerm ρ⊇ ⊢Δ ⊢t₂)
            (PE.subst₃ (_⊢_≡_∷_ _)
               (PE.cong (_∘⟨ _ ⟩ _) (PE.sym $ wk1-wk≡lift-wk1 _ _))
               (PE.cong (_∘⟨ _ ⟩ _) (PE.sym $ wk1-wk≡lift-wk1 _ _))
               PE.refl $
             wkEqTerm (lift ρ⊇) (∙ ⊢A′) t₁0≡t₂0)
            ok
        (fst-cong ⊢B t₁≡t₂) PE.refl →
          let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢B
              ⊢A′           = wk ρ⊇ ⊢Δ ⊢A ⦃ lt = <ˢ-trans A< ! ⦄
          in
          fst-cong (wk (lift ρ⊇) (∙ ⊢A′) ⊢B) (wkEqTerm ρ⊇ ⊢Δ t₁≡t₂)
        (snd-cong {G = B} ⊢B t₁≡t₂) PE.refl →
          let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢B
              ⊢A′           = wk ρ⊇ ⊢Δ ⊢A ⦃ lt = <ˢ-trans A< ! ⦄
          in
          PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ wk-β B) $
          snd-cong (wk (lift ρ⊇) (∙ ⊢A′) ⊢B) (wkEqTerm ρ⊇ ⊢Δ t₁≡t₂)
        (Σ-β₁ {G = B} ⊢B ⊢t ⊢u eq ok) PE.refl →
          let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢B
              ⊢A′           = wk ρ⊇ ⊢Δ ⊢A ⦃ lt = <ˢ-trans A< ! ⦄
          in
          Σ-β₁ (wk (lift ρ⊇) (∙ ⊢A′) ⊢B) (wkTerm ρ⊇ ⊢Δ ⊢t)
            (PE.subst (_⊢_∷_ _ _) (wk-β B) $
             wkTerm ρ⊇ ⊢Δ ⊢u)
            eq ok
        (Σ-β₂ {G = B} ⊢B ⊢t ⊢u eq ok) PE.refl →
          let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢B
              ⊢A′           = wk ρ⊇ ⊢Δ ⊢A ⦃ lt = <ˢ-trans A< ! ⦄
          in
          PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ wk-β B) $
          Σ-β₂ (wk (lift ρ⊇) (∙ ⊢A′) ⊢B) (wkTerm ρ⊇ ⊢Δ ⊢t)
            (PE.subst (_⊢_∷_ _ _) (wk-β B) $
             wkTerm ρ⊇ ⊢Δ ⊢u)
            eq ok
        (Σ-η {G = B} ⊢B ⊢t₁ ⊢t₂ fst-t₁≡fst-t₂ snd-t₁≡snd-t₂ ok)
          PE.refl →
          let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢B
              ⊢A′           = wk ρ⊇ ⊢Δ ⊢A ⦃ lt = <ˢ-trans A< ! ⦄
          in
          Σ-η (wk (lift ρ⊇) (∙ ⊢A′) ⊢B) (wkTerm ρ⊇ ⊢Δ ⊢t₁)
            (wkTerm ρ⊇ ⊢Δ ⊢t₂) (wkEqTerm ρ⊇ ⊢Δ fst-t₁≡fst-t₂)
            (PE.subst (_⊢_≡_∷_ _ _ _) (wk-β B) $
             wkEqTerm ρ⊇ ⊢Δ snd-t₁≡snd-t₂)
            ok
        (prod-cong {G = B} ⊢B t₁≡t₂ u₁≡u₂ ok) PE.refl →
          let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢B
              ⊢A′           = wk ρ⊇ ⊢Δ ⊢A ⦃ lt = <ˢ-trans A< ! ⦄
          in
          prod-cong (wk (lift ρ⊇) (∙ ⊢A′) ⊢B) (wkEqTerm ρ⊇ ⊢Δ t₁≡t₂)
            (PE.subst (_⊢_≡_∷_ _ _ _) (wk-β B) $
             wkEqTerm ρ⊇ ⊢Δ u₁≡u₂)
            ok
        (prodrec-cong {A = C} C₁≡C₂ t₁≡t₂ u₁≡u₂ ok) PE.refl →
          let _ , (⊢A , A<) , (⊢B , B<) = ∙∙⊢→⊢-<ˢ u₁≡u₂
              ⊢A′                       = wk ρ⊇ ⊢Δ ⊢A
                                            ⦃ lt = <ˢ-trans A< ! ⦄
              ⊢B′                       = wk (lift ρ⊇) (∙ ⊢A′) ⊢B
                                            ⦃ lt = <ˢ-trans B< ! ⦄
          in
          PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ wk-β C) $
          prodrec-cong (wkEq (lift ρ⊇) (∙ ΠΣⱼ ⊢B′ ok) C₁≡C₂)
            (wkEqTerm ρ⊇ ⊢Δ t₁≡t₂)
            (PE.subst (_⊢_≡_∷_ _ _ _) (wk-β-prodrec _ C) $
             wkEqTerm (lift (lift ρ⊇)) (∙ ⊢B′) u₁≡u₂)
            ok
        (prodrec-β {G = B} {A = C} {u = v} ⊢C ⊢t ⊢u ⊢v eq ok) PE.refl →
          let _ , (⊢A , A<) , (⊢B , B<) = ∙∙⊢→⊢-<ˢ ⊢v
              ⊢A′                       = wk ρ⊇ ⊢Δ ⊢A
                                            ⦃ lt = <ˢ-trans A< ! ⦄
              ⊢B′                       = wk (lift ρ⊇) (∙ ⊢A′) ⊢B
                                            ⦃ lt = <ˢ-trans B< ! ⦄
          in
          PE.subst₂ (_⊢_≡_∷_ _ _)
            (PE.sym $ wk-β-doubleSubst _ v _ _) (PE.sym $ wk-β C) $
          prodrec-β (wk (lift ρ⊇) (∙ ΠΣⱼ ⊢B′ ok) ⊢C)
            (wkTerm ρ⊇ ⊢Δ ⊢t)
            (PE.subst (_⊢_∷_ _ _) (wk-β B) $
             wkTerm ρ⊇ ⊢Δ ⊢u)
            (PE.subst (_⊢_∷_ _ _) (wk-β-prodrec _ C) $
             wkTerm (lift (lift ρ⊇)) (∙ ⊢B′) ⊢v)
            eq ok
        (emptyrec-cong A₁≡A₂ t₁≡t₂) PE.refl →
          emptyrec-cong (wkEq ρ⊇ ⊢Δ A₁≡A₂) (wkEqTerm ρ⊇ ⊢Δ t₁≡t₂)
        (unitrec-cong {A = A₁} A₁≡A₂ t₁≡t₂ u₁≡u₂ ok no-η) PE.refl →
          PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ wk-β A₁) $
          unitrec-cong
            (wkEq (lift ρ⊇) (∙ univ (Unitⱼ ⊢Δ ok)) A₁≡A₂)
            (wkEqTerm ρ⊇ ⊢Δ t₁≡t₂)
            (PE.subst (_⊢_≡_∷_ _ _ _) (wk-β A₁) $
             wkEqTerm ρ⊇ ⊢Δ u₁≡u₂)
            ok no-η
        (unitrec-β {A} ⊢A ⊢t ok no-η) PE.refl →
          PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ wk-β A) $
          unitrec-β (wk (lift ρ⊇) (∙ univ (Unitⱼ ⊢Δ ok)) ⊢A)
            (PE.subst (_⊢_∷_ _ _) (wk-β A) $
             wkTerm ρ⊇ ⊢Δ ⊢t)
            ok no-η
        (unitrec-β-η {A} ⊢A ⊢t ⊢u ok η) PE.refl →
          PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ wk-β A) $
          unitrec-β-η (wk (lift ρ⊇) (∙ univ (Unitⱼ ⊢Δ ok)) ⊢A)
            (wkTerm ρ⊇ ⊢Δ ⊢t)
            (PE.subst (_⊢_∷_ _ _) (wk-β A) $
             wkTerm ρ⊇ ⊢Δ ⊢u)
            ok η
        (η-unit ⊢t₁ ⊢t₂ η) PE.refl →
          η-unit (wkTerm ρ⊇ ⊢Δ ⊢t₁) (wkTerm ρ⊇ ⊢Δ ⊢t₂) η
        (suc-cong t₁≡t₂) PE.refl →
          suc-cong (wkEqTerm ρ⊇ ⊢Δ t₁≡t₂)
        (natrec-cong {A = A₁} A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂) PE.refl →
          let _ , (⊢A₁ , A₁<) = ∙⊢→⊢-<ˢ u₁≡u₂
              ⊢A₁′            = wk (lift ρ⊇) (∙ univ (ℕⱼ ⊢Δ)) ⊢A₁
                                  ⦃ lt = <ˢ-trans A₁< ! ⦄
          in
          PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ wk-β A₁) $
          natrec-cong (wkEq (lift ρ⊇) (∙ univ (ℕⱼ ⊢Δ)) A₁≡A₂)
            (PE.subst (_⊢_≡_∷_ _ _ _) (wk-β A₁) $
             wkEqTerm ρ⊇ ⊢Δ t₁≡t₂)
            (PE.subst (_⊢_≡_∷_ _ _ _) (wk-β-natrec _ A₁) $
             wkEqTerm (lift (lift ρ⊇)) (∙ ⊢A₁′) u₁≡u₂)
            (wkEqTerm ρ⊇ ⊢Δ v₁≡v₂)
        (natrec-zero {A} ⊢t ⊢u) PE.refl →
          let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢u
              ⊢A′           = wk (lift ρ⊇) (∙ univ (ℕⱼ ⊢Δ)) ⊢A
                                ⦃ lt = <ˢ-trans A< ! ⦄
          in
          PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ wk-β A) $
          natrec-zero
            (PE.subst (_⊢_∷_ _ _) (wk-β A) $
             wkTerm ρ⊇ ⊢Δ ⊢t)
            (PE.subst (_⊢_∷_ _ _) (wk-β-natrec _ A) $
             wkTerm (lift (lift ρ⊇)) (∙ ⊢A′) ⊢u)
        (natrec-suc {A} {s = u} ⊢t ⊢u ⊢v) PE.refl →
          let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢u
              ⊢A′           = wk (lift ρ⊇) (∙ univ (ℕⱼ ⊢Δ)) ⊢A
                                ⦃ lt = <ˢ-trans A< ! ⦄
          in
          PE.subst₂ (_⊢_≡_∷_ _ _)
            (PE.sym $ wk-β-doubleSubst _ u _ _) (PE.sym $ wk-β A) $
          natrec-suc
            (PE.subst (_⊢_∷_ _ _) (wk-β A) $
             wkTerm ρ⊇ ⊢Δ ⊢t)
            (PE.subst (_⊢_∷_ _ _) (wk-β-natrec _ A) $
             wkTerm (lift (lift ρ⊇)) (∙ ⊢A′) ⊢u)
            (wkTerm ρ⊇ ⊢Δ ⊢v)
        (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) PE.refl →
          Id-cong (wkEqTerm ρ⊇ ⊢Δ A₁≡A₂) (wkEqTerm ρ⊇ ⊢Δ t₁≡t₂)
            (wkEqTerm ρ⊇ ⊢Δ u₁≡u₂)
        (J-cong {B₁} A₁≡A₂ ⊢t₁ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ w₁≡w₂) PE.refl →
          let _ , (⊢A₁ , A₁<) , _ = ∙∙⊢→⊢-<ˢ B₁≡B₂
              ⊢A₁′                = wk ρ⊇ ⊢Δ ⊢A₁ ⦃ lt = <ˢ-trans A₁< ! ⦄
          in
          PE.subst (_⊢_≡_∷_ _ _ _)
            (PE.sym $ wk-β-doubleSubst _ B₁ _ _) $
          J-cong (wkEq ρ⊇ ⊢Δ A₁≡A₂) (wkTerm ρ⊇ ⊢Δ ⊢t₁)
            (wkEqTerm ρ⊇ ⊢Δ t₁≡t₂)
            (PE.subst₂ (λ A t → _ » _ ∙ U.wk _ _ ∙ Id A t _ ⊢ _ ≡ _)
               (PE.sym $ wk1-wk≡lift-wk1 _ _)
               (PE.sym $ wk1-wk≡lift-wk1 _ _) $
             wkEq (lift (lift ρ⊇))
               (∙ (Idⱼ
                     (PE.subst (_⊢_ _) (PE.sym $ lift-wk1 _ _) $
                      wk (step ρ⊇) (∙ ⊢A₁′) ⊢A₁
                        ⦃ lt = <ˢ-trans A₁< ! ⦄)
                     (PE.subst₂ (_ » _ ∙ U.wk _ _ ⊢_∷_)
                        (PE.sym $ lift-wk1 _ _)
                        (PE.sym $ lift-wk1 _ _) $
                      wkTerm (step ρ⊇) (∙ ⊢A₁′) ⊢t₁)
                     (PE.subst (_ » _ ∙ U.wk _ _ ⊢ _ ∷_)
                        (wk1-wk≡lift-wk1 _ _) $
                      var₀ ⊢A₁′)))
               B₁≡B₂)
            (PE.subst (_⊢_≡_∷_ _ _ _) (wk-β-doubleSubst _ B₁ _ _) $
             wkEqTerm ρ⊇ ⊢Δ u₁≡u₂)
            (wkEqTerm ρ⊇ ⊢Δ v₁≡v₂) (wkEqTerm ρ⊇ ⊢Δ w₁≡w₂)
        (J-β {B} ⊢t ⊢B ⊢u eq) PE.refl →
          let _ , (⊢A , A<) , _ = ∙∙⊢→⊢-<ˢ ⊢B
              ⊢A′               = wk ρ⊇ ⊢Δ ⊢A ⦃ lt = <ˢ-trans A< ! ⦄
          in
          PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ wk-β-doubleSubst _ B _ _) $
          J-β (wkTerm ρ⊇ ⊢Δ ⊢t)
            (PE.subst₂ (λ A t → _ » _ ∙ U.wk _ _ ∙ Id A t _ ⊢ _)
               (PE.sym $ wk1-wk≡lift-wk1 _ _)
               (PE.sym $ wk1-wk≡lift-wk1 _ _) $
             wk (lift (lift ρ⊇))
               (∙ (Idⱼ
                     (PE.subst (_⊢_ _) (PE.sym $ lift-wk1 _ _) $
                      wk (step ρ⊇) (∙ ⊢A′) ⊢A ⦃ lt = <ˢ-trans A< ! ⦄)
                     (PE.subst₂ (_⊢_∷_ _)
                        (PE.sym $ lift-wk1 _ _)
                        (PE.sym $ lift-wk1 _ _) $
                      wkTerm (step ρ⊇) (∙ ⊢A′) ⊢t)
                     (PE.subst (_⊢_∷_ _ _) (wk1-wk≡lift-wk1 _ _) $
                      var₀ ⊢A′)))
               ⊢B)
            (PE.subst (_⊢_∷_ _ _) (wk-β-doubleSubst _ B _ _) $
             wkTerm ρ⊇ ⊢Δ ⊢u)
            (PE.cong (U.wk _) eq)
        (K-cong {B₁} A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ ok) PE.refl →
          let _ , ⊢Id                       = ∙⊢→⊢-<ˢ B₁≡B₂
              (⊢A₁ , A₁<) , (⊢t₁ , t₁<) , _ = inversion-Id-⊢-<ˢ ⊢Id
              ⊢A₁′                          = wk ρ⊇ ⊢Δ ⊢A₁
                                                ⦃ lt = <ˢ-trans A₁< ! ⦄
              ⊢t₁′                          = wkTerm ρ⊇ ⊢Δ ⊢t₁
                                                ⦃ lt = <ˢ-trans t₁< ! ⦄
          in
          PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ wk-β B₁) $
          K-cong (wkEq ρ⊇ ⊢Δ A₁≡A₂) (wkEqTerm ρ⊇ ⊢Δ t₁≡t₂)
            (wkEq (lift ρ⊇) (∙ Idⱼ ⊢A₁′ ⊢t₁′ ⊢t₁′) B₁≡B₂)
            (PE.subst (_⊢_≡_∷_ _ _ _) (wk-β B₁) $
             wkEqTerm ρ⊇ ⊢Δ u₁≡u₂)
            (wkEqTerm ρ⊇ ⊢Δ v₁≡v₂) ok
        (K-β {B} ⊢B ⊢u ok) PE.refl →
          let _ , ⊢Id                   = ∙⊢→⊢-<ˢ ⊢B
              (⊢A , A<) , (⊢t , t<) , _ = inversion-Id-⊢-<ˢ ⊢Id
              ⊢A′                       = wk ρ⊇ ⊢Δ ⊢A
                                            ⦃ lt = <ˢ-trans A< ! ⦄
              ⊢t′                       = wkTerm ρ⊇ ⊢Δ ⊢t
                                            ⦃ lt = <ˢ-trans t< ! ⦄
          in
          PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ wk-β B) $
          K-β (wk (lift ρ⊇) (∙ Idⱼ ⊢A′ ⊢t′ ⊢t′) ⊢B)
            (PE.subst (_⊢_∷_ _ _) (wk-β B) $
             wkTerm ρ⊇ ⊢Δ ⊢u)
            ok
        ([]-cong-cong l₁≡l₂ A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ ok) PE.refl →
          PE.subst (_⊢_≡_∷_ _ _ _) (wk-Id-Erased _) $
          []-cong-cong (wkEqLevel ρ⊇ ⊢Δ l₁≡l₂) (wkEq ρ⊇ ⊢Δ A₁≡A₂)
            (wkEqTerm ρ⊇ ⊢Δ t₁≡t₂) (wkEqTerm ρ⊇ ⊢Δ u₁≡u₂)
            (wkEqTerm ρ⊇ ⊢Δ v₁≡v₂) ok
        ([]-cong-β ⊢l ⊢t eq ok) PE.refl →
          PE.subst (_⊢_≡_∷_ _ _ _) (wk-Id-Erased _) $
          []-cong-β (wkLevel ρ⊇ ⊢Δ ⊢l) (wkTerm ρ⊇ ⊢Δ ⊢t)
            (PE.cong (U.wk _) eq) ok
        (equality-reflection ok ⊢Id ⊢v) PE.refl →
          equality-reflection ok (wk ρ⊇ ⊢Δ ⊢Id) (wkTerm ρ⊇ ⊢Δ ⊢v)
      where
      open Variants hyp

  opaque
    unfolding size

    -- A weakening lemma for _⊢_≡_∷Level.

    wkEqLevel′ :
      (∀ {s₁} → s₁ <ˢ s₂ → P s₁) →
      ρ ∷ Δ ⊇ Γ → ∇ »⊢ Δ →
      (l₁≡l₂ : ∇ » Γ ⊢ l₁ ≡ l₂ ∷Level) →
      size l₁≡l₂ PE.≡ s₂ →
      ∇ » Δ ⊢ U.wk ρ l₁ ≡ U.wk ρ l₂ ∷Level
    wkEqLevel′ hyp ρ⊇ ⊢Δ = λ where
        (term ok l₁≡l₂) PE.refl →
          term ok (wkEqTerm ρ⊇ ⊢Δ l₁≡l₂)
        (literal ok _) _ →
          literal (Allowed-literal-wk-⇔ .proj₂ ok) ⊢Δ
      where
      open Variants hyp

  opaque

    -- The type P s is inhabited for every s.

    P-inhabited : P s
    P-inhabited =
      well-founded-induction P
        (λ _ hyp →
           record
             { wk        = wk′        hyp
             ; wkTerm    = wkTerm′    hyp
             ; wkLevel   = wkLevel′   hyp
             ; wkEq      = wkEq′      hyp
             ; wkEqTerm  = wkEqTerm′  hyp
             ; wkEqLevel = wkEqLevel′ hyp
             })
        _

opaque
  unfolding _»_∷ʷ_⊇_

  -- A weakening lemma for _⊢[_].

  wk : ∇ » ρ ∷ʷ Δ ⊇ Γ → ∇ » Γ ⊢[ 𝓙 ] → ∇ » Δ ⊢[ mapJ (U.wk ρ) 𝓙 ]
  wk {𝓙 = [ctxt]} (_ , ⊢Δ) _ =
    ⊢Δ
  wk {𝓙 = [ _ type]} (ρ⊇ , ⊢Δ) ⊢𝓙 =
    P.wk Inhabited.P-inhabited ρ⊇ ⊢Δ ⊢𝓙 PE.refl
  wk {𝓙 = [ _ ≡ _ type]} (ρ⊇ , ⊢Δ) ⊢𝓙 =
    P.wkEq Inhabited.P-inhabited ρ⊇ ⊢Δ ⊢𝓙 PE.refl
  wk {𝓙 = [ _ ∷ A ]} (ρ⊇ , ⊢Δ) ⊢𝓙 =
    P.wkTerm Inhabited.P-inhabited ρ⊇ ⊢Δ ⊢𝓙 PE.refl
  wk {𝓙 = [ _ ≡ _ ∷ A ]} (ρ⊇ , ⊢Δ) ⊢𝓙 =
    P.wkEqTerm Inhabited.P-inhabited ρ⊇ ⊢Δ ⊢𝓙 PE.refl
  wk {𝓙 = [ _ ∷Level]} (ρ⊇ , ⊢Δ) ⊢𝓙 =
    P.wkLevel Inhabited.P-inhabited ρ⊇ ⊢Δ ⊢𝓙 PE.refl
  wk {𝓙 = [ _ ≡ _ ∷Level]} (ρ⊇ , ⊢Δ) ⊢𝓙 =
    P.wkEqLevel Inhabited.P-inhabited ρ⊇ ⊢Δ ⊢𝓙 PE.refl

opaque
  unfolding _⊢_≤ₗ_∷Level

  -- A weakening lemma for _⊢_≤ₗ_∷Level.

  wk-≤ₗ∷L :
    ∇ » ρ ∷ʷ Δ ⊇ Γ → ∇ » Γ ⊢ l₁ ≤ₗ l₂ ∷Level →
    ∇ » Δ ⊢ U.wk ρ l₁ ≤ₗ U.wk ρ l₂ ∷Level
  wk-≤ₗ∷L ρ⊇ (⊢l₁ , l₁⊔l₂≡l₂) =
    wk ρ⊇ ⊢l₁ ,
    PE.subst (flip (_⊢_≡_∷Level _) _) wk-supᵘₗ (wk ρ⊇ l₁⊔l₂≡l₂)

opaque

  -- A special case of wk.

  wk₁ : ∇ » Γ ⊢ A → ∇ » Γ ⊢[ 𝓙 ] → ∇ » Γ ∙ A ⊢[ mapJ U.wk1 𝓙 ]
  wk₁ ⊢A = wk (stepʷ id ⊢A)

mutual
  wkRed : ∇ » ρ ∷ʷ Δ ⊇ Γ → ∇ » Γ ⊢ A ⇒ B → ∇ » Δ ⊢ U.wk ρ A ⇒ U.wk ρ B
  wkRed ρ (univ A⇒B) = univ (wkRedTerm ρ A⇒B)

  wkRedTerm :
    ∇ » ρ ∷ʷ Δ ⊇ Γ → ∇ » Γ ⊢ t ⇒ u ∷ A → ∇ » Δ ⊢ U.wk ρ t ⇒ U.wk ρ u ∷ U.wk ρ A
  wkRedTerm ρ (conv t⇒u A≡B) = conv (wkRedTerm ρ t⇒u) (wk ρ A≡B)
  wkRedTerm ρ (δ-red ⊢Γ α↦t PE.refl PE.refl) =
    δ-red (wf-∷ʷ⊇ ρ) α↦t (wk₀-comp _ _) (wk₀-comp _ _)
  wkRedTerm ρ (supᵘ-zeroˡ ⊢l) = supᵘ-zeroˡ (wk ρ ⊢l)
  wkRedTerm {ρ} [ρ] (supᵘ-zeroʳ ⊢l) = supᵘ-zeroʳ (wk [ρ] ⊢l)
  wkRedTerm ρ (supᵘ-sucᵘ ⊢l₁ ⊢l₂) = supᵘ-sucᵘ (wk ρ ⊢l₁) (wk ρ ⊢l₂)
  wkRedTerm ρ (supᵘ-substˡ t⇒t′ ⊢u) = supᵘ-substˡ (wkRedTerm ρ t⇒t′) (wk ρ ⊢u)
  wkRedTerm {ρ} [ρ] (supᵘ-substʳ ⊢t u⇒u′) = supᵘ-substʳ (wk [ρ] ⊢t) (wkRedTerm [ρ] u⇒u′)
  wkRedTerm ρ (lower-subst x) = lower-subst (wkRedTerm ρ x)
  wkRedTerm ρ (Lift-β ⊢A x₁) = Lift-β (wk ρ ⊢A) (wk ρ x₁)
  wkRedTerm ρ (app-subst {B} t⇒u a) =
    PE.subst (λ x → _ ⊢ _ ⇒ _ ∷ x) (PE.sym (wk-β B))
             (app-subst (wkRedTerm ρ t⇒u) (wk ρ a))
  wkRedTerm ρ (β-red {B} {t} ⊢B ⊢t ⊢u p≡q ok) =
    let ρ⇑ = liftʷʷ ρ (wk ρ (⊢∙→⊢ (wf ⊢B))) in
    PE.subst₂ (_⊢_⇒_∷_ _ _) (PE.sym (wk-β t)) (PE.sym (wk-β B)) $
    β-red (wk ρ⇑ ⊢B) (wk ρ⇑ ⊢t) (wk ρ ⊢u) p≡q ok
  wkRedTerm ρ (fst-subst ⊢G t⇒) =
    let ρF = wk ρ (⊢∙→⊢ (wf ⊢G))
        ρG = wk (liftʷʷ ρ ρF) ⊢G
        ρt⇒ = wkRedTerm ρ t⇒
    in  fst-subst ρG ρt⇒
  wkRedTerm ρ (snd-subst {G} ⊢G t⇒) =
    let ρF = wk ρ (⊢∙→⊢ (wf ⊢G))
        ρG = wk (liftʷʷ ρ ρF) ⊢G
        ρt⇒ = wkRedTerm ρ t⇒
    in  PE.subst (λ x → _ ⊢ snd _ _ ⇒ snd _ _ ∷ x) (PE.sym (wk-β G))
      (snd-subst ρG ρt⇒)
  wkRedTerm {ρ} [ρ] (Σ-β₁ {G} ⊢G t u p≡p′ ok) =
    let ρF = wk [ρ] (⊢∙→⊢ (wf ⊢G))
        ρG = wk (liftʷʷ [ρ] ρF) ⊢G
        ρt = wk [ρ] t
        ρu = wk [ρ] u
        ρu = PE.subst (λ x → _ ⊢ _ ∷ x) (wk-β G) ρu
    in  Σ-β₁ ρG ρt ρu p≡p′ ok
  wkRedTerm {ρ} [ρ] (Σ-β₂ {G} ⊢G t u p≡p′ ok) =
    let ρF = wk [ρ] (⊢∙→⊢ (wf ⊢G))
        ρG = wk (liftʷʷ [ρ] ρF) ⊢G
        ρt = wk [ρ] t
        ρu = wk [ρ] u
        ρu = PE.subst (λ x → _ ⊢ _ ∷ x) (wk-β G) ρu
    in  PE.subst (λ x → _ ⊢ _ ⇒ _ ∷ x) (PE.sym (wk-β G))
      (Σ-β₂ ρG ρt ρu p≡p′ ok)
  wkRedTerm {ρ} {Δ} [ρ] (prodrec-subst {A} ⊢A ⊢u t⇒t′ ok) =
    let ⊢G = ⊢∙→⊢ (wf ⊢u)
        ρF = wk [ρ] (⊢∙→⊢ (wf ⊢G))
        ρG = wk (liftʷʷ [ρ] ρF) ⊢G
        ρA = wk (liftʷʷ [ρ] (ΠΣⱼ ρG ok)) ⊢A
        ρt⇒t′ = wkRedTerm [ρ] t⇒t′
        ρu = wk (liftʷ (lift (∷ʷ⊇→∷⊇ [ρ])) ρG) ⊢u
    in  PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym (wk-β A))
                 (prodrec-subst ρA
                               (PE.subst (λ x → _ ⊢ _ ∷ x)
                                         (wk-β-prodrec ρ A) ρu)
                               ρt⇒t′ ok)
  wkRedTerm {ρ} {Δ} [ρ] (prodrec-β {G} {A} {u} ⊢A ⊢t ⊢t′ ⊢u p≡p′ ok) =
    let ⊢G = ⊢∙→⊢ (wf ⊢u)
        ρF = wk [ρ] (⊢∙→⊢ (wf ⊢G))
        ρG = wk (liftʷʷ [ρ] ρF) ⊢G
        ρA = wk (liftʷʷ [ρ] (ΠΣⱼ ρG ok)) ⊢A
        ρt = wk [ρ] ⊢t
        ρt′ = wk [ρ] ⊢t′
        ρu = wk (liftʷ (lift (∷ʷ⊇→∷⊇ [ρ])) ρG) ⊢u
    in  PE.subst₂ (λ x y → _ ⊢ prodrec _ _ _ _ _ _ ⇒ x ∷ y)
          (PE.trans (subst-wk u)
            (PE.trans (substVar-to-subst
                         (λ where
                            x0      → PE.refl
                            (x0 +1) → PE.refl
                            (x +2)  → PE.refl)
                         u)
            (PE.sym (wk-subst u))))
          (PE.sym (wk-β A))
          (prodrec-β ρA ρt
             (PE.subst (λ x → _ ⊢ _ ∷ x) (wk-β G) ρt′)
             (PE.subst (λ x → _ ⊢ _ ∷ x) (wk-β-prodrec ρ A) ρu)
             p≡p′ ok)
  wkRedTerm [ρ] (natrec-subst {A = F} ⊢z ⊢s n⇒n′) =
    PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym (wk-β F)) $
    natrec-subst (PE.subst (_⊢_∷_ _ _) (wk-β F) (wk [ρ] ⊢z))
      (PE.subst (_⊢_∷_ _ _) (wk-β-natrec _ F) $
       wk
         (liftʷ (lift (∷ʷ⊇→∷⊇ [ρ])) $
          wk (liftʷʷ [ρ] (univ (ℕⱼ (wf-∷ʷ⊇ [ρ])))) (⊢∙→⊢ (wf ⊢s)))
         ⊢s)
      (wkRedTerm [ρ] n⇒n′)
  wkRedTerm [ρ] (natrec-zero {A = F} ⊢z ⊢s) =
    PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym (wk-β F)) $
    natrec-zero (PE.subst (_⊢_∷_ _ _) (wk-β F) (wk [ρ] ⊢z))
      (PE.subst (_⊢_∷_ _ _) (wk-β-natrec _ F) $
       wk
         (liftʷ (lift (∷ʷ⊇→∷⊇ [ρ])) $
          wk (liftʷʷ [ρ] (univ (ℕⱼ (wf-∷ʷ⊇ [ρ])))) (⊢∙→⊢ (wf ⊢s)))
         ⊢s)
  wkRedTerm [ρ] (natrec-suc {A} {s} ⊢z ⊢s ⊢n) =
    PE.subst₂ (_⊢_⇒_∷_ _ _)
      (PE.sym (wk-β-doubleSubst _ s _ _))
      (PE.sym (wk-β A)) $
    natrec-suc (PE.subst (_⊢_∷_ _ _) (wk-β A) (wk [ρ] ⊢z))
      (PE.subst (_⊢_∷_ _ _) (wk-β-natrec _ A) $
       wk
         (liftʷ (lift (∷ʷ⊇→∷⊇ [ρ])) $
          wk (liftʷʷ [ρ] (univ (ℕⱼ (wf-∷ʷ⊇ [ρ])))) (⊢∙→⊢ (wf ⊢s)))
         ⊢s)
      (wk [ρ] ⊢n)
  wkRedTerm [ρ] (emptyrec-subst ⊢A n⇒n′) =
    emptyrec-subst (wk [ρ] ⊢A) (wkRedTerm [ρ] n⇒n′)
  wkRedTerm [ρ] (unitrec-subst {A} ⊢A ⊢u t⇒t′ ok₁ ok₂) =
    let ρA = wk (liftʷʷ [ρ] (univ (Unitⱼ (wf-∷ʷ⊇ [ρ]) ok₁))) ⊢A
        ρu = wk [ρ] ⊢u
        ρu′ = PE.subst (λ x → _ ⊢ _ ∷ x) (wk-β A) ρu
        ρt⇒t′ = wkRedTerm [ρ] t⇒t′
    in  PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym (wk-β A))
          (unitrec-subst ρA ρu′ ρt⇒t′ ok₁ ok₂)
  wkRedTerm [ρ] (unitrec-β {A} ⊢A ⊢u ok₁ ok₂) =
    let ρA = wk (liftʷʷ [ρ] (univ (Unitⱼ (wf-∷ʷ⊇ [ρ]) ok₁))) ⊢A
        ρu = wk [ρ] ⊢u
        ρu′ = PE.subst (λ x → _ ⊢ _ ∷ x) (wk-β A) ρu
    in  PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym (wk-β A))
          (unitrec-β ρA ρu′ ok₁ ok₂)
  wkRedTerm ρ (unitrec-β-η {A} ⊢A ⊢t ⊢u ok₁ ok₂) =
    PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym (wk-β A)) $
    unitrec-β-η (wk (liftʷʷ ρ (univ (Unitⱼ (wf-∷ʷ⊇ ρ) ok₁))) ⊢A)
      (wk ρ ⊢t) (PE.subst (_⊢_∷_ _ _) (wk-β A) (wk ρ ⊢u)) ok₁
      ok₂
  wkRedTerm ρ (J-subst {B} ⊢t ⊢B ⊢u ⊢t′ ⊢v) =
    PE.subst (_ ⊢ U.wk _ (J _ _ _ _ _ _ _ _) ⇒ _ ∷_)
      (PE.sym $ wk-β-doubleSubst _ B _ _) $
    J-subst (wk ρ ⊢t)
      (PE.subst₂ (λ A t → _ » _ ∙ U.wk _ _ ∙ Id A t _ ⊢ _)
         (PE.sym $ wk1-wk≡lift-wk1 _ _)
         (PE.sym $ wk1-wk≡lift-wk1 _ _) $
       wk
         (liftʷ (lift (∷ʷ⊇→∷⊇ ρ)) $
          Idⱼ
            (PE.subst (_⊢_ _) (PE.sym $ lift-wk1 _ _) $
             wk step-ρ ⊢A)
            (PE.subst₂ (_⊢_∷_ _)
               (PE.sym $ lift-wk1 _ _)
               (PE.sym $ lift-wk1 _ _) $
             wk step-ρ ⊢t)
            (PE.subst (_⊢_∷_ _ _) (wk1-wk≡lift-wk1 _ _) $
             var₀ ⊢A′))
         ⊢B)
      (PE.subst (_ ⊢ _ ∷_)
         (wk-β-doubleSubst _ B _ _) $
       wk ρ ⊢u)
      (wk ρ ⊢t′) (wkRedTerm ρ ⊢v)
    where
    ⊢A     = ⊢∙→⊢ (wf (⊢∙→⊢ (wf ⊢B)))
    ⊢A′    = wk ρ ⊢A
    step-ρ = stepʷʷ ρ ⊢A′
  wkRedTerm ρ (K-subst {B} ⊢B ⊢u ⊢v ok) =
    PE.subst (_ ⊢ U.wk _ (K _ _ _ _ _ _) ⇒ _ ∷_)
      (PE.sym $ wk-β B) $
    K-subst (wk (liftʷʷ ρ (wk ρ (⊢∙→⊢ (wf ⊢B)))) ⊢B)
      (PE.subst (_ ⊢ _ ∷_) (wk-β B) $
       wk ρ ⊢u)
      (wkRedTerm ρ ⊢v) ok
  wkRedTerm ρ ([]-cong-subst l v ok) =
    PE.subst (_⊢_⇒_∷_ _ _ _) (wk-Id-Erased _) $
    []-cong-subst (wk ρ l) (wkRedTerm ρ v) ok
  wkRedTerm ρ (J-β {B} ⊢t ⊢t′ t≡t′ ⊢B B≡B ⊢u) =
    PE.subst (_ ⊢ U.wk _ (J _ _ _ _ _ _ _ rfl) ⇒ _ ∷_)
      (PE.sym $ wk-β-doubleSubst _ B _ _) $
    J-β (wk ρ ⊢t) (wk ρ ⊢t′) (wk ρ t≡t′)
      (PE.subst₂ (λ A t → _ » _ ∙ U.wk _ _ ∙ Id A t _ ⊢ _)
         (PE.sym $ wk1-wk≡lift-wk1 _ _)
         (PE.sym $ wk1-wk≡lift-wk1 _ _) $
       wk
         (liftʷ (lift (∷ʷ⊇→∷⊇ ρ)) $
          Idⱼ
            (PE.subst (_⊢_ _) (PE.sym $ lift-wk1 _ _) $
             wk step-ρ ⊢A)
            (PE.subst₂ (_⊢_∷_ _)
               (PE.sym $ lift-wk1 _ _)
               (PE.sym $ lift-wk1 _ _) $
             wk step-ρ ⊢t)
            (PE.subst (_⊢_∷_ _ _) (wk1-wk≡lift-wk1 _ _) $
             var₀ ⊢A′))
         ⊢B)
      (PE.subst₂ (_ ⊢_≡_)
         (wk-β-doubleSubst _ B _ _)
         (wk-β-doubleSubst _ B _ _)
         (wk ρ B≡B))
      (PE.subst (_ ⊢ _ ∷_) (wk-β-doubleSubst _ B _ _) $
       wk ρ ⊢u)
    where
    ⊢A     = ⊢∙→⊢ (wf (⊢∙→⊢ (wf ⊢B)))
    ⊢A′    = wk ρ ⊢A
    step-ρ = stepʷʷ ρ ⊢A′
  wkRedTerm ρ (K-β {B} ⊢B ⊢u ok) =
    PE.subst (_ ⊢ U.wk _ (K _ _ _ _ _ rfl) ⇒ _ ∷_)
      (PE.sym $ wk-β B) $
    K-β (wk (liftʷʷ ρ (wk ρ (⊢∙→⊢ (wf ⊢B)))) ⊢B)
      (PE.subst (_ ⊢ _ ∷_) (wk-β B) $
       wk ρ ⊢u)
      ok
  wkRedTerm ρ ([]-cong-β ⊢l t≡t′ ok) =
    PE.subst (_⊢_⇒_∷_ _ _ _) (wk-Id-Erased _) $
    []-cong-β (wk ρ ⊢l) (wk ρ t≡t′) ok

wkRed* : ∇ » ρ ∷ʷ Δ ⊇ Γ → ∇ » Γ ⊢ A ⇒* B → ∇ » Δ ⊢ U.wk ρ A ⇒* U.wk ρ B
wkRed* ρ (id A)         = id (wk ρ A)
wkRed* ρ (A⇒A′ ⇨ A′⇒*B) = wkRed ρ A⇒A′ ⇨ wkRed* ρ A′⇒*B

wkRed*Term :
  ∇ » ρ ∷ʷ Δ ⊇ Γ → ∇ » Γ ⊢ t ⇒* u ∷ A → ∇ » Δ ⊢ U.wk ρ t ⇒* U.wk ρ u ∷ U.wk ρ A
wkRed*Term ρ (id t)         = id (wk ρ t)
wkRed*Term ρ (t⇒t′ ⇨ t′⇒*u) = wkRedTerm ρ t⇒t′ ⇨ wkRed*Term ρ t′⇒*u

opaque

  -- Weakening for _⊢_↘_.

  wkRed↘ : ∇ » ρ ∷ʷ Δ ⊇ Γ → ∇ » Γ ⊢ A ↘ B → ∇ » Δ ⊢ U.wk ρ A ↘ U.wk ρ B
  wkRed↘ ρ⊇ = Σ.map (wkRed* ρ⊇) (wkWhnf _)

opaque

  -- Weakening for _⊢_↘_∷_.

  wkRed↘Term :
    ∇ » ρ ∷ʷ Δ ⊇ Γ → ∇ » Γ ⊢ t ↘ u ∷ A → ∇ » Δ ⊢ U.wk ρ t ↘ U.wk ρ u ∷ U.wk ρ A
  wkRed↘Term ρ⊇ = Σ.map (wkRed*Term ρ⊇) (wkWhnf _)

opaque mutual

  -- A typing rule for _∙[_][_][_]ʷ.

  ⊢[][][]ʷ : ∇ » ρ ∷ʷ Δ ⊇ drop k Γ → ∇ »⊢ Γ → ∇ »⊢ Δ ∙[ k ][ Γ ][ ρ ]ʷ
  ⊢[][][]ʷ {k = 0}    ρ∷ _      = wf-∷ʷ⊇ ρ∷
  ⊢[][][]ʷ {k = 1+ _} ρ∷ (∙ ⊢A) = ∙ wk (liftnʷ ρ∷ (wf ⊢A)) ⊢A

  -- A "constructor" for _∷ʷ_⊇_.

  liftnʷ :
    ∇ » ρ ∷ʷ Δ ⊇ drop k Γ → ∇ »⊢ Γ →
    ∇ » liftn ρ k ∷ʷ Δ ∙[ k ][ Γ ][ ρ ]ʷ ⊇ Γ
  liftnʷ ρ∷ ⊢Γ = ∷⊇→∷ʷ⊇ (liftn∷⊇ (∷ʷ⊇→∷⊇ ρ∷)) (⊢[][][]ʷ ρ∷ ⊢Γ)
