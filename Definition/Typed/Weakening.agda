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

open Modality 𝕄
open Type-restrictions R

open import Definition.Untyped M as U hiding (wk; wk′)
open import Definition.Untyped.Allowed-literal R
open import Definition.Untyped.Erased 𝕄 hiding ([_])
open import Definition.Untyped.Inversion M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M
open import Definition.Untyped.Quotient 𝕄
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
open import Tools.Reasoning.PropositionalEquality
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

opaque
  unfolding Quot-rel-Con

  -- A weakening lemma related to Quot-rel-Con.

  lift-Quot-rel-Con :
    ρ ∷ Δ ⊇ Γ →
    liftn ρ 2 ∷ Quot-rel-Con Δ (U.wk ρ A) ⊇ Quot-rel-Con Γ A
  lift-Quot-rel-Con ρ⊇ =
    PE.subst (flip (_∷_⊇_ _) _ ∘→ _∙_ _)
      (PE.sym (wk1-wk≡lift-wk1 _ _)) $
    lift (lift ρ⊇)

opaque
  unfolding Quot-rel-Con Resp-Con

  -- A weakening lemma related to Resp-Con.

  lift-Resp-Con :
    ρ ∷ Δ ⊇ Γ →
    liftn ρ 3 ∷ Resp-Con Δ (U.wk ρ A) (U.wk (liftn ρ 2) B) ⊇
      Resp-Con Γ A B
  lift-Resp-Con ρ⊇ =
    PE.subst (flip (_∷_⊇_ _) _)
      (PE.cong (flip _∙_ _ ∘→ _∙_ _) (wk⇑[]-wk[]≡ 1)) $
    lift (lift (lift ρ⊇))

opaque
  unfolding Is-set-Con

  -- A weakening lemma related to Is-set-Con.

  lift-Is-set-Con :
    ρ ∷ Δ ⊇ Γ →
    liftn ρ 5 ∷
      Is-set-Con Δ (U.wk ρ A) (U.wk (liftn ρ 2) B) (U.wk (lift ρ) C) ⊇
      Is-set-Con Γ A B C
  lift-Is-set-Con {C} ρ⊇ =
    PE.subst (flip (_∷_⊇_ _) _)
      (PE.cong₂ _∙_
         (PE.cong₂ _∙_ (PE.cong (_∙_ _) (wk⇑[]-wk[]≡ 1))
            (PE.cong₃ Id (wk⇑[]-wk[]≡ 2) PE.refl PE.refl))
         (PE.cong₃ Id (wk⇑[]-wk[]≡ 3) PE.refl PE.refl)) $
    lift (lift (lift (lift (lift ρ⊇))))

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

  -- A variant of liftʷ.

  liftⁿʷ :
    ρ ∷ Δ ⊇ drop k Γ →
    ∇ »⊢ Δ ∙[ k ][ Γ ][ ρ ]ʷ →
    ∇ » liftn ρ k ∷ʷ Δ ∙[ k ][ Γ ][ ρ ]ʷ ⊇ Γ
  liftⁿʷ {k = 0}                ⊢ρ ⊢Δ     = ∷⊇→∷ʷ⊇ ⊢ρ ⊢Δ
  liftⁿʷ {k = 1+ k} {Γ = _ ∙ _} ⊢ρ (∙ ⊢A) =
    liftʷʷ (liftⁿʷ ⊢ρ (wf ⊢A)) ⊢A

opaque

  -- A variant of liftⁿʷ.

  liftⁿʷʷ :
    ∇ » ρ ∷ʷ Δ ⊇ drop k Γ →
    ∇ »⊢ Δ ∙[ k ][ Γ ][ ρ ]ʷ →
    ∇ » liftn ρ k ∷ʷ Δ ∙[ k ][ Γ ][ ρ ]ʷ ⊇ Γ
  liftⁿʷʷ = liftⁿʷ ∘→ ∷ʷ⊇→∷⊇

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

-- A variant of the fields of P, along with some lemmas.

private module Variants (hyp : ∀ {s₁} → s₁ <ˢ s₂ → P s₁) where

  opaque

    -- A variant of the fields of P.

    wk :
      ∀ {𝓙} → ρ ∷ Δ ⊇ Γ → ∇ »⊢ Δ →
      (⊢𝓙 : ∇ » Γ ⊢[ 𝓙 ])
      ⦃ lt : size ⊢𝓙 <ˢ s₂ ⦄ →
      ∇ » Δ ⊢[ mapJ (U.wk ρ) 𝓙 ]
    wk {𝓙 = [ctxt]} _ ⊢Δ _ =
      ⊢Δ
    wk {𝓙 = [ _ type]} ρ⊇ ⊢Δ ⊢𝓙 ⦃ lt ⦄ =
      P.wk (hyp lt) ρ⊇ ⊢Δ ⊢𝓙 PE.refl
    wk {𝓙 = [ _ ≡ _ type]} ρ⊇ ⊢Δ ⊢𝓙 ⦃ lt ⦄ =
      P.wkEq (hyp lt) ρ⊇ ⊢Δ ⊢𝓙 PE.refl
    wk {𝓙 = [ _ ∷ _ ]} ρ⊇ ⊢Δ ⊢𝓙 ⦃ lt ⦄ =
      P.wkTerm (hyp lt) ρ⊇ ⊢Δ ⊢𝓙 PE.refl
    wk {𝓙 = [ _ ≡ _ ∷ _ ]} ρ⊇ ⊢Δ ⊢𝓙 ⦃ lt ⦄ =
      P.wkEqTerm (hyp lt) ρ⊇ ⊢Δ ⊢𝓙 PE.refl
    wk {𝓙 = [ _ ∷Level]} ρ⊇ ⊢Δ ⊢𝓙 ⦃ lt ⦄ =
      P.wkLevel (hyp lt) ρ⊇ ⊢Δ ⊢𝓙 PE.refl
    wk {𝓙 = [ _ ≡ _ ∷Level]} ρ⊇ ⊢Δ ⊢𝓙 ⦃ lt ⦄ =
      P.wkEqLevel (hyp lt) ρ⊇ ⊢Δ ⊢𝓙 PE.refl

  opaque
    unfolding Quot-rel-Con

    -- A derived definition.

    wk-Quot-rel-Con :
      ρ ∷ Δ ⊇ Γ → ∇ »⊢ Δ →
      (⊢A : ∇ » Γ ⊢ A)
      ⦃ lt : size ⊢A <ˢ s₂ ⦄ →
      ∇ »⊢ Quot-rel-Con Δ (U.wk ρ A)
    wk-Quot-rel-Con ρ⊇ ⊢Δ ⊢A =
      ∙_ $
      PE.subst (_⊢_ _) (PE.sym (wk-comp _ _ _)) $
      wk (step ρ⊇) (∙ wk ρ⊇ ⊢Δ ⊢A) ⊢A

  opaque
    unfolding Quot-rel-Con

    -- A derived definition.

    wk-Quot-rel-Con-⊢ :
      ∀ {𝓙} → ρ ∷ Δ ⊇ Γ → ∇ »⊢ Δ →
      (⊢𝓙 : ∇ » Quot-rel-Con Γ A ⊢[ 𝓙 ])
      ⦃ lt : size ⊢𝓙 <ˢ s₂ ⦄ →
      ∇ » Quot-rel-Con Δ (U.wk ρ A) ⊢[ mapJ (U.wk (liftn ρ 2)) 𝓙 ]
    wk-Quot-rel-Con-⊢ ρ⊇ ⊢Δ ⊢𝓙 =
      let _ , (⊢A , A<) , _ = ∙∙⊢→⊢-<ˢ ⊢𝓙 in
      wk (lift-Quot-rel-Con ρ⊇)
        (wk-Quot-rel-Con ρ⊇ ⊢Δ ⊢A ⦃ lt = <ˢ-trans A< ! ⦄) ⊢𝓙

  opaque
    unfolding Resp-Con

    -- A derived definition.

    wk-Resp-Con :
      ρ ∷ Δ ⊇ Γ → ∇ »⊢ Δ →
      (⊢B : ∇ » Quot-rel-Con Γ A ⊢ B)
      ⦃ lt : size ⊢B <ˢ s₂ ⦄ →
      ∇ »⊢ Resp-Con Δ (U.wk ρ A) (U.wk (liftn ρ 2) B)
    wk-Resp-Con ρ⊇ ⊢Δ ⊢B =
      ∙ wk-Quot-rel-Con-⊢ ρ⊇ ⊢Δ ⊢B

  opaque
    unfolding Is-set-Con

    -- A derived definition.

    wk-Is-set-Con :
      ρ ∷ Δ ⊇ Γ → ∇ »⊢ Δ →
      (⊢C : ∇ » Γ ∙ Quot A B ⊢ C)
      ⦃ lt : size ⊢C <ˢ s₂ ⦄ →
      ∇ »⊢
        Is-set-Con Δ (U.wk ρ A) (U.wk (liftn ρ 2) B) (U.wk (lift ρ) C)
    wk-Is-set-Con {ρ} {Δ} {∇} {A} {B} {C} ρ⊇ ⊢Δ ⊢C =
      ∙_ $
      PE.subst (flip _⊢_ _)
        (PE.cong (_»_ _) $
         PE.cong₂ _∙_
           (PE.cong (_∙_ _) (PE.sym (wk-comp _ _ _)))
           (PE.cong₃ Id (PE.sym (wk-comp _ _ _)) PE.refl PE.refl)) $
      Idⱼ
        (PE.subst (_⊢_ _) (PE.sym (wk-comp _ _ _)) $
         wk (step (step (step (lift ρ⊇)))) (∙ ⊢Id) ⊢C)
        (PE.subst (_⊢_∷_ _ _) wk[]≡wk[]′ (var₂ ⊢Id))
        (PE.subst (_⊢_∷_ _ _)
           (PE.trans (PE.cong wk[ 2 ] (PE.sym (wk-comp _ _ _)))
            wk[]≡wk[]′)
           (var₁ ⊢Id))
      where
      ⊢C′ : (∇ » Δ) »∙ U.wk ρ (Quot A B) ⊢ U.wk (lift ρ) C
      ⊢C′ =
        let _ , (⊢Q , Q<) = ∙⊢→⊢-<ˢ ⊢C
            ⊢Q′           = wk ρ⊇ ⊢Δ ⊢Q ⦃ lt = <ˢ-trans Q< ! ⦄
        in
        wk (lift ρ⊇) (∙ ⊢Q′) ⊢C

      ⊢C″ :
        (∇ » Δ) »∙ U.wk ρ (Quot A B) »∙ U.wk (lift ρ) C ⊢
        U.wk (step (lift ρ)) C
      ⊢C″ = wk (step (lift ρ⊇)) (∙ ⊢C′) ⊢C

      ⊢Id :
        (∇ » Δ) »∙ U.wk ρ (Quot A B) »∙ U.wk (lift ρ) C »∙
        U.wk (step (lift ρ)) C ⊢
        Id (U.wk (stepn (lift ρ) 2) C) (var x1) (var x0)
      ⊢Id =
        Idⱼ
          (wk (step (step (lift ρ⊇))) (∙ ⊢C″) ⊢C)
          (PE.subst (_⊢_∷_ _ _)
             (PE.trans (wk[]≡wk[]′ {n = 2}) (wk-comp _ _ _)) $
           var₁ ⊢C″)
          (PE.subst (_⊢_∷_ _ _)
             (PE.trans (wk[]≡wk[]′ {n = 1}) (wk-comp _ _ _)) $
           var₀ ⊢C″)

-- The type P s is inhabited for every s.

private module Inhabited where

  opaque
    unfolding Quot-rel-Con size

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
          univ (wk ρ⊇ ⊢Δ ⊢A)
        (Liftⱼ ⊢l ⊢A) PE.refl →
          Liftⱼ (wk ρ⊇ ⊢Δ ⊢l) (wk ρ⊇ ⊢Δ ⊢A)
        (ΠΣⱼ ⊢B ok) PE.refl →
          let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢B
              ⊢A′           = wk ρ⊇ ⊢Δ ⊢A ⦃ lt = <ˢ-trans A< ! ⦄
          in
          ΠΣⱼ (wk (lift ρ⊇) (∙ ⊢A′) ⊢B) ok
        (Idⱼ ⊢A ⊢t ⊢u) PE.refl →
          Idⱼ (wk ρ⊇ ⊢Δ ⊢A) (wk ρ⊇ ⊢Δ ⊢t) (wk ρ⊇ ⊢Δ ⊢u)
        (Quot ok ⊢B) PE.refl →
          Quot ok (wk-Quot-rel-Con-⊢ ρ⊇ ⊢Δ ⊢B)
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
          conv (wk ρ⊇ ⊢Δ ⊢t) (wk ρ⊇ ⊢Δ B≡A)
        (var _ x∈) _ →
          var ⊢Δ (wkIndex ρ⊇ x∈)
        (defn ⊢Γ α↦t PE.refl) PE.refl →
          defn ⊢Δ α↦t (wk₀-comp _ _)
        (Levelⱼ _ ok) _ →
          Levelⱼ ⊢Δ ok
        (zeroᵘⱼ ok _) _ →
          zeroᵘⱼ ok ⊢Δ
        (sucᵘⱼ ⊢t) PE.refl →
          sucᵘⱼ (wk ρ⊇ ⊢Δ ⊢t)
        (supᵘⱼ ⊢t ⊢u) PE.refl →
          supᵘⱼ (wk ρ⊇ ⊢Δ ⊢t) (wk ρ⊇ ⊢Δ ⊢u)
        (Uⱼ l) PE.refl →
          PE.subst (_⊢_∷_ _ _) (PE.cong U $ PE.sym wk-1ᵘ+) $
          Uⱼ (wk ρ⊇ ⊢Δ l)
        (Liftⱼ ⊢l₁ ⊢l₂ ⊢A) PE.refl →
          PE.subst (_⊢_∷_ _ _) (PE.cong U $ PE.sym wk-supᵘₗ) $
          Liftⱼ (wk ρ⊇ ⊢Δ ⊢l₁) (wk ρ⊇ ⊢Δ ⊢l₂) (wk ρ⊇ ⊢Δ ⊢A)
        (liftⱼ ⊢l₂ ⊢A ⊢t) PE.refl →
          liftⱼ (wk ρ⊇ ⊢Δ ⊢l₂) (wk ρ⊇ ⊢Δ ⊢A) (wk ρ⊇ ⊢Δ ⊢t)
        (lowerⱼ ⊢t) PE.refl →
          lowerⱼ (wk ρ⊇ ⊢Δ ⊢t)
        (ΠΣⱼ l ⊢A ⊢B ok) PE.refl →
          let ⊢A′ = wk ρ⊇ ⊢Δ ⊢A in
          ΠΣⱼ (wk ρ⊇ ⊢Δ l) ⊢A′
            (PE.subst (λ x → _ ⊢ _ ∷ U x)
              (PE.sym $ wk1-wk≡lift-wk1 _ _)
              (wk (lift ρ⊇) (∙ univ ⊢A′) ⊢B))
            ok
        (lamⱼ ⊢B ⊢t ok) PE.refl →
          let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢t
              ⊢A′           = wk ρ⊇ ⊢Δ ⊢A ⦃ lt = <ˢ-trans A< ! ⦄
          in
          lamⱼ (wk (lift ρ⊇) (∙ ⊢A′) ⊢B) (wk (lift ρ⊇) (∙ ⊢A′) ⊢t) ok
        (_∘ⱼ_ {G = B} ⊢t ⊢u) PE.refl →
          PE.subst (_⊢_∷_ _ _) (PE.sym $ wk-β B)
            (wk ρ⊇ ⊢Δ ⊢t ∘ⱼ wk ρ⊇ ⊢Δ ⊢u)
        (prodⱼ {G = B} ⊢B ⊢t ⊢u ok) PE.refl →
          let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢B
              ⊢A′           = wk ρ⊇ ⊢Δ ⊢A ⦃ lt = <ˢ-trans A< ! ⦄
          in
          prodⱼ (wk (lift ρ⊇) (∙ ⊢A′) ⊢B) (wk ρ⊇ ⊢Δ ⊢t)
            (PE.subst (_⊢_∷_ _ _) (wk-β B) $
             wk ρ⊇ ⊢Δ ⊢u)
            ok
        (fstⱼ ⊢B ⊢t) PE.refl →
          let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢B
              ⊢A′           = wk ρ⊇ ⊢Δ ⊢A ⦃ lt = <ˢ-trans A< ! ⦄
          in
          fstⱼ (wk (lift ρ⊇) (∙ ⊢A′) ⊢B) (wk ρ⊇ ⊢Δ ⊢t)
        (sndⱼ {G = B} ⊢B ⊢t) PE.refl →
          let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢B
              ⊢A′           = wk ρ⊇ ⊢Δ ⊢A ⦃ lt = <ˢ-trans A< ! ⦄
          in
          PE.subst (_⊢_∷_ _ _) (PE.sym $ wk-β B) $
          sndⱼ (wk (lift ρ⊇) (∙ ⊢A′) ⊢B) (wk ρ⊇ ⊢Δ ⊢t)
        (prodrecⱼ {A = C} ⊢C ⊢t ⊢u) PE.refl →
          let _ , _ , ok                = inversion-ΠΣ (⊢∙→⊢ (wf ⊢C))
              _ , (⊢A , A<) , (⊢B , B<) = ∙∙⊢→⊢-<ˢ ⊢u
              ⊢A′                       = wk ρ⊇ ⊢Δ ⊢A
                                            ⦃ lt = <ˢ-trans A< ! ⦄
              ⊢B′                       = wk (lift ρ⊇) (∙ ⊢A′) ⊢B
                                            ⦃ lt = <ˢ-trans B< ! ⦄
          in
          PE.subst (_⊢_∷_ _ _) (PE.sym $ wk-β C) $
          prodrecⱼ (wk (lift ρ⊇) (∙ ΠΣⱼ ⊢B′ ok) ⊢C) (wk ρ⊇ ⊢Δ ⊢t)
            (PE.subst (_⊢_∷_ _ _) (wk-β-prodrec _ C) $
             wk (lift (lift ρ⊇)) (∙ ⊢B′) ⊢u)
        (Emptyⱼ _) _ →
          Emptyⱼ ⊢Δ
        (emptyrecⱼ ⊢A ⊢t) PE.refl →
          emptyrecⱼ (wk ρ⊇ ⊢Δ ⊢A) (wk ρ⊇ ⊢Δ ⊢t)
        (starⱼ ⊢Γ ok) PE.refl →
          starⱼ ⊢Δ ok
        (unitrecⱼ {A} ⊢A ⊢t ⊢u) PE.refl →
          let ok = inversion-Unit (⊢∙→⊢ (wf ⊢A)) in
          PE.subst (_⊢_∷_ _ _) (PE.sym $ wk-β A) $
          unitrecⱼ (wk (lift ρ⊇) (∙ univ (Unitⱼ ⊢Δ ok)) ⊢A)
            (wk ρ⊇ ⊢Δ ⊢t)
            (PE.subst (_⊢_∷_ _ _) (wk-β A) $
             wk ρ⊇ ⊢Δ ⊢u)
        (Unitⱼ _ ok) PE.refl →
          Unitⱼ ⊢Δ ok
        (ℕⱼ _) _ →
          ℕⱼ ⊢Δ
        (zeroⱼ _) _ →
          zeroⱼ ⊢Δ
        (sucⱼ ⊢t) PE.refl →
          sucⱼ (wk ρ⊇ ⊢Δ ⊢t)
        (natrecⱼ {A} ⊢t ⊢u ⊢v) PE.refl →
          let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢u
              ⊢A′           = wk (lift ρ⊇) (∙ univ (ℕⱼ ⊢Δ)) ⊢A
                                ⦃ lt = <ˢ-trans A< ! ⦄
          in
          PE.subst (_⊢_∷_ _ _) (PE.sym $ wk-β A) $
          natrecⱼ
            (PE.subst (_⊢_∷_ _ _) (wk-β A) $
             wk ρ⊇ ⊢Δ ⊢t)
            (PE.subst (_⊢_∷_ _ _) (wk-β-natrec _ A) $
             wk (lift (lift ρ⊇)) (∙ ⊢A′) ⊢u)
            (wk ρ⊇ ⊢Δ ⊢v)
        (Idⱼ ⊢A ⊢t ⊢u) PE.refl →
          Idⱼ (wk ρ⊇ ⊢Δ ⊢A) (wk ρ⊇ ⊢Δ ⊢t) (wk ρ⊇ ⊢Δ ⊢u)
        (rflⱼ ⊢t) PE.refl →
          rflⱼ (wk ρ⊇ ⊢Δ ⊢t)
        (Jⱼ {B} ⊢t ⊢B ⊢u ⊢v ⊢w) PE.refl →
          let _ , (⊢A , A<) , _ = ∙∙⊢→⊢-<ˢ ⊢B
              ⊢A′               = wk ρ⊇ ⊢Δ ⊢A ⦃ lt = <ˢ-trans A< ! ⦄
          in
          PE.subst (_⊢_∷_ _ _) (PE.sym $ wk-β-doubleSubst _ B _ _) $
          Jⱼ (wk ρ⊇ ⊢Δ ⊢t)
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
                      wk (step ρ⊇) (∙ ⊢A′) ⊢t)
                     (PE.subst (_⊢_∷_ _ _) (wk1-wk≡lift-wk1 _ _) $
                      var₀ ⊢A′)))
               ⊢B)
            (PE.subst (_⊢_∷_ _ _) (wk-β-doubleSubst _ B _ _) $
             wk ρ⊇ ⊢Δ ⊢u)
            (wk ρ⊇ ⊢Δ ⊢v) (wk ρ⊇ ⊢Δ ⊢w)
        (Kⱼ {B} ⊢B ⊢u ⊢v ok) PE.refl →
          let _ , ⊢Id                   = ∙⊢→⊢-<ˢ ⊢B
              (⊢A , A<) , (⊢t , t<) , _ = inversion-Id-⊢-<ˢ ⊢Id
              ⊢A′                       = wk ρ⊇ ⊢Δ ⊢A
                                            ⦃ lt = <ˢ-trans A< ! ⦄
              ⊢t′                       = wk ρ⊇ ⊢Δ ⊢t
                                            ⦃ lt = <ˢ-trans t< ! ⦄
          in
          PE.subst (_⊢_∷_ _ _) (PE.sym $ wk-β B) $
          Kⱼ (wk (lift ρ⊇) (∙ Idⱼ ⊢A′ ⊢t′ ⊢t′) ⊢B)
            (PE.subst (_⊢_∷_ _ _) (wk-β B) $
             wk ρ⊇ ⊢Δ ⊢u)
            (wk ρ⊇ ⊢Δ ⊢v) ok
        ([]-congⱼ ⊢l ⊢A ⊢t ⊢u ⊢v ok) PE.refl →
          PE.subst (_⊢_∷_ _ _) (wk-Id-Erased _) $
          []-congⱼ (wk ρ⊇ ⊢Δ ⊢l) (wk ρ⊇ ⊢Δ ⊢A) (wk ρ⊇ ⊢Δ ⊢t)
            (wk ρ⊇ ⊢Δ ⊢u) (wk ρ⊇ ⊢Δ ⊢v) ok
        (Quot ok ⊢l ⊢A ⊢B) PE.refl →
          Quot ok (wk ρ⊇ ⊢Δ ⊢l) (wk ρ⊇ ⊢Δ ⊢A)
            (PE.subst (_⊢_∷_ _ _) (wk⇑[]-wk[]≡ 2) $
             wk-Quot-rel-Con-⊢ ρ⊇ ⊢Δ ⊢B)
        (class ⊢Q ⊢t) PE.refl →
          class (wk ρ⊇ ⊢Δ ⊢Q) (wk ρ⊇ ⊢Δ ⊢t)
        (resp {B} ⊢Q ⊢t ⊢u ⊢v) PE.refl →
          resp (wk ρ⊇ ⊢Δ ⊢Q) (wk ρ⊇ ⊢Δ ⊢t) (wk ρ⊇ ⊢Δ ⊢u)
            (PE.subst (_⊢_∷_ _ _) (wk-β-doubleSubst _ B _ _) $
             wk ρ⊇ ⊢Δ ⊢v)
        (set ⊢Q ⊢t ⊢u ⊢v ⊢w) PE.refl →
          set (wk ρ⊇ ⊢Δ ⊢Q) (wk ρ⊇ ⊢Δ ⊢t) (wk ρ⊇ ⊢Δ ⊢u) (wk ρ⊇ ⊢Δ ⊢v)
            (wk ρ⊇ ⊢Δ ⊢w)
        ⊢q@(qrec {C} ⊢C ⊢t ⊢u ⊢v ⊢w) PE.refl →
          let _ , (⊢A , A<) , (⊢B , B<) , _ , (⊢Q , Q<) =
                inversion-Is-set-Cons ⊢v

              instance
                _ : size ⊢Q <ˢ size ⊢q
                _ = <ˢ-trans Q< !

                _ : size ⊢A <ˢ size ⊢q
                _ = <ˢ-trans A< !

                _ : size ⊢B <ˢ size ⊢q
                _ = <ˢ-trans B< !
          in
          PE.subst (_⊢_∷_ _ _) (PE.sym (wk-β C)) $
          qrec (wk (lift ρ⊇) (∙ wk ρ⊇ ⊢Δ ⊢Q) ⊢C)
            (PE.subst (_⊢_∷_ _ _) (wk-β↑ C) $
             wk (lift ρ⊇) (∙ wk ρ⊇ ⊢Δ ⊢A) ⊢t)
            (PE.subst (_⊢_∷_ _ _) wk-Resp-type $
             wk (lift-Resp-Con ρ⊇) (wk-Resp-Con ρ⊇ ⊢Δ ⊢B) ⊢u)
            (PE.subst (_⊢_∷_ _ _) wk-Is-set-type $
             wk (lift-Is-set-Con ρ⊇) (wk-Is-set-Con ρ⊇ ⊢Δ ⊢C) ⊢v)
            (wk ρ⊇ ⊢Δ ⊢w)
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
        (term ok ⊢l)   PE.refl → term ok (wk ρ⊇ ⊢Δ ⊢l)
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
          univ (wk ρ⊇ ⊢Δ A₁≡A₂)
        (refl ⊢A) PE.refl →
          refl (wk ρ⊇ ⊢Δ ⊢A)
        (sym A₂≡A₁) PE.refl →
          sym (wk ρ⊇ ⊢Δ A₂≡A₁)
        (trans A₁≡A₂ A₂≡A₃) PE.refl →
          trans (wk ρ⊇ ⊢Δ A₁≡A₂) (wk ρ⊇ ⊢Δ A₂≡A₃)
        (U-cong l₁≡l₂) PE.refl →
          U-cong (wk ρ⊇ ⊢Δ l₁≡l₂)
        (Lift-cong l₁≡l₂ A≡B) PE.refl →
          Lift-cong (wk ρ⊇ ⊢Δ l₁≡l₂) (wk ρ⊇ ⊢Δ A≡B)
        (ΠΣ-cong A₁≡A₂ B₁≡B₂ ok) PE.refl →
          let _ , (⊢A₁ , A₁<) = ∙⊢→⊢-<ˢ B₁≡B₂
              ⊢A₁′            = wk ρ⊇ ⊢Δ ⊢A₁ ⦃ lt = <ˢ-trans A₁< ! ⦄
          in
          ΠΣ-cong (wk ρ⊇ ⊢Δ A₁≡A₂) (wk (lift ρ⊇) (∙ ⊢A₁′) B₁≡B₂) ok
        (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) PE.refl →
          Id-cong (wk ρ⊇ ⊢Δ A₁≡A₂) (wk ρ⊇ ⊢Δ t₁≡t₂) (wk ρ⊇ ⊢Δ u₁≡u₂)
        (Quot-cong ok A₁≡A₂ B₁≡B₂) PE.refl →
          Quot-cong ok (wk ρ⊇ ⊢Δ A₁≡A₂) (wk-Quot-rel-Con-⊢ ρ⊇ ⊢Δ B₁≡B₂)
      where
      open Variants hyp

  opaque
    unfolding Is-set-Con Resp-Con size

    -- A weakening lemma for _⊢_≡_∷_.

    wkEqTerm′ :
      (∀ {s₁} → s₁ <ˢ s₂ → P s₁) →
      ρ ∷ Δ ⊇ Γ → ∇ »⊢ Δ →
      (t₁≡t₂ : ∇ » Γ ⊢ t₁ ≡ t₂ ∷ A) →
      size t₁≡t₂ PE.≡ s₂ →
      ∇ » Δ ⊢ U.wk ρ t₁ ≡ U.wk ρ t₂ ∷ U.wk ρ A
    wkEqTerm′ hyp ρ⊇ ⊢Δ = λ where
        (refl ⊢t) PE.refl →
          refl (wk ρ⊇ ⊢Δ ⊢t)
        (sym ⊢A t₂≡t₁) PE.refl →
          sym (wk ρ⊇ ⊢Δ ⊢A) (wk ρ⊇ ⊢Δ t₂≡t₁)
        (trans t₁≡t₂ t₂≡t₃) PE.refl →
          trans (wk ρ⊇ ⊢Δ t₁≡t₂) (wk ρ⊇ ⊢Δ t₂≡t₃)
        (conv t₁≡t₂ B≡A) PE.refl →
          conv (wk ρ⊇ ⊢Δ t₁≡t₂) (wk ρ⊇ ⊢Δ B≡A)
        (δ-red ⊢Γ α↦t PE.refl PE.refl) PE.refl →
          δ-red ⊢Δ α↦t (wk₀-comp _ _) (wk₀-comp _ _)
        (sucᵘ-cong t₁≡t₂) PE.refl →
          sucᵘ-cong (wk ρ⊇ ⊢Δ t₁≡t₂)
        (supᵘ-cong t₁≡t₂ u₁≡u₂) PE.refl →
          supᵘ-cong (wk ρ⊇ ⊢Δ t₁≡t₂) (wk ρ⊇ ⊢Δ u₁≡u₂)
        (supᵘ-zeroˡ l) PE.refl →
          supᵘ-zeroˡ (wk ρ⊇ ⊢Δ l)
        (supᵘ-sucᵘ l₁ l₂) PE.refl →
          supᵘ-sucᵘ (wk ρ⊇ ⊢Δ l₁) (wk ρ⊇ ⊢Δ l₂)
        (supᵘ-assoc l₁ l₂ l₃) PE.refl →
          supᵘ-assoc (wk ρ⊇ ⊢Δ l₁) (wk ρ⊇ ⊢Δ l₂) (wk ρ⊇ ⊢Δ l₃)
        (supᵘ-comm l₁ l₂) PE.refl →
          supᵘ-comm (wk ρ⊇ ⊢Δ l₁) (wk ρ⊇ ⊢Δ l₂)
        (supᵘ-idem ⊢l) PE.refl →
          supᵘ-idem (wk ρ⊇ ⊢Δ ⊢l)
        (supᵘ-sub ⊢l) PE.refl →
          supᵘ-sub (wk ρ⊇ ⊢Δ ⊢l)
        (U-cong l₁≡l₂) PE.refl →
          U-cong (wk ρ⊇ ⊢Δ l₁≡l₂)
        (Lift-cong ⊢l₁ ⊢l₂ l₂≡l₂′ A≡B) PE.refl →
          PE.subst (_⊢_≡_∷_ _ _ _) (PE.cong U $ PE.sym wk-supᵘₗ) $
          Lift-cong (wk ρ⊇ ⊢Δ ⊢l₁) (wk ρ⊇ ⊢Δ ⊢l₂) (wk ρ⊇ ⊢Δ l₂≡l₂′)
            (wk ρ⊇ ⊢Δ A≡B)
        (lower-cong t≡u) PE.refl →
          lower-cong (wk ρ⊇ ⊢Δ t≡u)
        (Lift-β ⊢A ⊢t) PE.refl →
          Lift-β (wk ρ⊇ ⊢Δ ⊢A) (wk ρ⊇ ⊢Δ ⊢t)
        (Lift-η ⊢l₂ ⊢A ⊢t ⊢u t≡u) PE.refl →
          Lift-η (wk ρ⊇ ⊢Δ ⊢l₂) (wk ρ⊇ ⊢Δ ⊢A) (wk ρ⊇ ⊢Δ ⊢t)
            (wk ρ⊇ ⊢Δ ⊢u) (wk ρ⊇ ⊢Δ t≡u)
        (ΠΣ-cong ⊢l A₁≡A₂ B₁≡B₂ ok) PE.refl →
          let _ , (⊢A₁ , A₁<) = ∙⊢→⊢-<ˢ B₁≡B₂
              ⊢A₁′            = wk ρ⊇ ⊢Δ ⊢A₁ ⦃ lt = <ˢ-trans A₁< ! ⦄
          in
          ΠΣ-cong (wk ρ⊇ ⊢Δ ⊢l) (wk ρ⊇ ⊢Δ A₁≡A₂)
            (PE.subst (λ x → _ ⊢ _ ≡ _ ∷ U x)
              (PE.sym $ wk1-wk≡lift-wk1 _ _)
              (wk (lift ρ⊇) (∙ ⊢A₁′) B₁≡B₂))
            ok
        (app-cong {G = B} t₁≡t₂ u₁≡u₂) PE.refl →
          PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ wk-β B) $
          app-cong (wk ρ⊇ ⊢Δ t₁≡t₂) (wk ρ⊇ ⊢Δ u₁≡u₂)
        (β-red {B} {t} ⊢B ⊢t ⊢u eq ok) PE.refl →
          let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢B
              ⊢A′           = wk ρ⊇ ⊢Δ ⊢A ⦃ lt = <ˢ-trans A< ! ⦄
          in
          PE.subst₂ (_⊢_≡_∷_ _ _) (PE.sym $ wk-β t) (PE.sym $ wk-β B) $
          β-red (wk (lift ρ⊇) (∙ ⊢A′) ⊢B) (wk (lift ρ⊇) (∙ ⊢A′) ⊢t)
            (wk ρ⊇ ⊢Δ ⊢u) eq ok
        (η-eq {f = t₁} {g = t₂} ⊢B ⊢t₁ ⊢t₂ t₁0≡t₂0 ok) PE.refl →
          let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ t₁0≡t₂0
              ⊢A′           = wk ρ⊇ ⊢Δ ⊢A ⦃ lt = <ˢ-trans A< ! ⦄
          in
          η-eq (wk (lift ρ⊇) (∙ ⊢A′) ⊢B) (wk ρ⊇ ⊢Δ ⊢t₁)
            (wk ρ⊇ ⊢Δ ⊢t₂)
            (PE.subst₃ (_⊢_≡_∷_ _)
               (PE.cong (_∘⟨ _ ⟩ _) (PE.sym $ wk1-wk≡lift-wk1 _ _))
               (PE.cong (_∘⟨ _ ⟩ _) (PE.sym $ wk1-wk≡lift-wk1 _ _))
               PE.refl $
             wk (lift ρ⊇) (∙ ⊢A′) t₁0≡t₂0)
            ok
        (fst-cong ⊢B t₁≡t₂) PE.refl →
          let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢B
              ⊢A′           = wk ρ⊇ ⊢Δ ⊢A ⦃ lt = <ˢ-trans A< ! ⦄
          in
          fst-cong (wk (lift ρ⊇) (∙ ⊢A′) ⊢B) (wk ρ⊇ ⊢Δ t₁≡t₂)
        (snd-cong {G = B} ⊢B t₁≡t₂) PE.refl →
          let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢B
              ⊢A′           = wk ρ⊇ ⊢Δ ⊢A ⦃ lt = <ˢ-trans A< ! ⦄
          in
          PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ wk-β B) $
          snd-cong (wk (lift ρ⊇) (∙ ⊢A′) ⊢B) (wk ρ⊇ ⊢Δ t₁≡t₂)
        (Σ-β₁ {G = B} ⊢B ⊢t ⊢u eq ok) PE.refl →
          let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢B
              ⊢A′           = wk ρ⊇ ⊢Δ ⊢A ⦃ lt = <ˢ-trans A< ! ⦄
          in
          Σ-β₁ (wk (lift ρ⊇) (∙ ⊢A′) ⊢B) (wk ρ⊇ ⊢Δ ⊢t)
            (PE.subst (_⊢_∷_ _ _) (wk-β B) $
             wk ρ⊇ ⊢Δ ⊢u)
            eq ok
        (Σ-β₂ {G = B} ⊢B ⊢t ⊢u eq ok) PE.refl →
          let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢B
              ⊢A′           = wk ρ⊇ ⊢Δ ⊢A ⦃ lt = <ˢ-trans A< ! ⦄
          in
          PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ wk-β B) $
          Σ-β₂ (wk (lift ρ⊇) (∙ ⊢A′) ⊢B) (wk ρ⊇ ⊢Δ ⊢t)
            (PE.subst (_⊢_∷_ _ _) (wk-β B) $
             wk ρ⊇ ⊢Δ ⊢u)
            eq ok
        (Σ-η {G = B} ⊢B ⊢t₁ ⊢t₂ fst-t₁≡fst-t₂ snd-t₁≡snd-t₂ ok)
          PE.refl →
          let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢B
              ⊢A′           = wk ρ⊇ ⊢Δ ⊢A ⦃ lt = <ˢ-trans A< ! ⦄
          in
          Σ-η (wk (lift ρ⊇) (∙ ⊢A′) ⊢B) (wk ρ⊇ ⊢Δ ⊢t₁)
            (wk ρ⊇ ⊢Δ ⊢t₂) (wk ρ⊇ ⊢Δ fst-t₁≡fst-t₂)
            (PE.subst (_⊢_≡_∷_ _ _ _) (wk-β B) $
             wk ρ⊇ ⊢Δ snd-t₁≡snd-t₂)
            ok
        (prod-cong {G = B} ⊢B t₁≡t₂ u₁≡u₂ ok) PE.refl →
          let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢B
              ⊢A′           = wk ρ⊇ ⊢Δ ⊢A ⦃ lt = <ˢ-trans A< ! ⦄
          in
          prod-cong (wk (lift ρ⊇) (∙ ⊢A′) ⊢B) (wk ρ⊇ ⊢Δ t₁≡t₂)
            (PE.subst (_⊢_≡_∷_ _ _ _) (wk-β B) $
             wk ρ⊇ ⊢Δ u₁≡u₂)
            ok
        (prodrec-cong {A = C} C₁≡C₂ t₁≡t₂ u₁≡u₂) PE.refl →
          let _ , _ , ok                = inversion-ΠΣ (⊢∙→⊢ (wf C₁≡C₂))
              _ , (⊢A , A<) , (⊢B , B<) = ∙∙⊢→⊢-<ˢ u₁≡u₂
              ⊢A′                       = wk ρ⊇ ⊢Δ ⊢A
                                            ⦃ lt = <ˢ-trans A< ! ⦄
              ⊢B′                       = wk (lift ρ⊇) (∙ ⊢A′) ⊢B
                                            ⦃ lt = <ˢ-trans B< ! ⦄
          in
          PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ wk-β C) $
          prodrec-cong (wk (lift ρ⊇) (∙ ΠΣⱼ ⊢B′ ok) C₁≡C₂)
            (wk ρ⊇ ⊢Δ t₁≡t₂)
            (PE.subst (_⊢_≡_∷_ _ _ _) (wk-β-prodrec _ C) $
             wk (lift (lift ρ⊇)) (∙ ⊢B′) u₁≡u₂)
        (prodrec-β {G = B} {A = C} {u = v} ⊢C ⊢t ⊢u ⊢v eq) PE.refl →
          let _ , _ , ok                = inversion-ΠΣ (⊢∙→⊢ (wf ⊢C))
              _ , (⊢A , A<) , (⊢B , B<) = ∙∙⊢→⊢-<ˢ ⊢v
              ⊢A′                       = wk ρ⊇ ⊢Δ ⊢A
                                            ⦃ lt = <ˢ-trans A< ! ⦄
              ⊢B′                       = wk (lift ρ⊇) (∙ ⊢A′) ⊢B
                                            ⦃ lt = <ˢ-trans B< ! ⦄
          in
          PE.subst₂ (_⊢_≡_∷_ _ _)
            (PE.sym $ wk-β-doubleSubst _ v _ _) (PE.sym $ wk-β C) $
          prodrec-β (wk (lift ρ⊇) (∙ ΠΣⱼ ⊢B′ ok) ⊢C)
            (wk ρ⊇ ⊢Δ ⊢t)
            (PE.subst (_⊢_∷_ _ _) (wk-β B) $
             wk ρ⊇ ⊢Δ ⊢u)
            (PE.subst (_⊢_∷_ _ _) (wk-β-prodrec _ C) $
             wk (lift (lift ρ⊇)) (∙ ⊢B′) ⊢v)
            eq
        (emptyrec-cong A₁≡A₂ t₁≡t₂) PE.refl →
          emptyrec-cong (wk ρ⊇ ⊢Δ A₁≡A₂) (wk ρ⊇ ⊢Δ t₁≡t₂)
        (unitrec-cong {A = A₁} A₁≡A₂ t₁≡t₂ u₁≡u₂ no-η) PE.refl →
          let ok = inversion-Unit (⊢∙→⊢ (wf A₁≡A₂)) in
          PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ wk-β A₁) $
          unitrec-cong
            (wk (lift ρ⊇) (∙ univ (Unitⱼ ⊢Δ ok)) A₁≡A₂)
            (wk ρ⊇ ⊢Δ t₁≡t₂)
            (PE.subst (_⊢_≡_∷_ _ _ _) (wk-β A₁) $
             wk ρ⊇ ⊢Δ u₁≡u₂)
            no-η
        (unitrec-β {A} ⊢A ⊢t no-η) PE.refl →
          let ok = inversion-Unit (⊢∙→⊢ (wf ⊢A)) in
          PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ wk-β A) $
          unitrec-β (wk (lift ρ⊇) (∙ univ (Unitⱼ ⊢Δ ok)) ⊢A)
            (PE.subst (_⊢_∷_ _ _) (wk-β A) $
             wk ρ⊇ ⊢Δ ⊢t)
            no-η
        (unitrec-β-η {A} ⊢A ⊢t ⊢u η) PE.refl →
          let ok = inversion-Unit (⊢∙→⊢ (wf ⊢A)) in
          PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ wk-β A) $
          unitrec-β-η (wk (lift ρ⊇) (∙ univ (Unitⱼ ⊢Δ ok)) ⊢A)
            (wk ρ⊇ ⊢Δ ⊢t)
            (PE.subst (_⊢_∷_ _ _) (wk-β A) $
             wk ρ⊇ ⊢Δ ⊢u)
            η
        (η-unit ⊢t₁ ⊢t₂ η) PE.refl →
          η-unit (wk ρ⊇ ⊢Δ ⊢t₁) (wk ρ⊇ ⊢Δ ⊢t₂) η
        (suc-cong t₁≡t₂) PE.refl →
          suc-cong (wk ρ⊇ ⊢Δ t₁≡t₂)
        (natrec-cong {A = A₁} A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂) PE.refl →
          let _ , (⊢A₁ , A₁<) = ∙⊢→⊢-<ˢ u₁≡u₂
              ⊢A₁′            = wk (lift ρ⊇) (∙ univ (ℕⱼ ⊢Δ)) ⊢A₁
                                  ⦃ lt = <ˢ-trans A₁< ! ⦄
          in
          PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ wk-β A₁) $
          natrec-cong (wk (lift ρ⊇) (∙ univ (ℕⱼ ⊢Δ)) A₁≡A₂)
            (PE.subst (_⊢_≡_∷_ _ _ _) (wk-β A₁) $
             wk ρ⊇ ⊢Δ t₁≡t₂)
            (PE.subst (_⊢_≡_∷_ _ _ _) (wk-β-natrec _ A₁) $
             wk (lift (lift ρ⊇)) (∙ ⊢A₁′) u₁≡u₂)
            (wk ρ⊇ ⊢Δ v₁≡v₂)
        (natrec-zero {A} ⊢t ⊢u) PE.refl →
          let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢u
              ⊢A′           = wk (lift ρ⊇) (∙ univ (ℕⱼ ⊢Δ)) ⊢A
                                ⦃ lt = <ˢ-trans A< ! ⦄
          in
          PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ wk-β A) $
          natrec-zero
            (PE.subst (_⊢_∷_ _ _) (wk-β A) $
             wk ρ⊇ ⊢Δ ⊢t)
            (PE.subst (_⊢_∷_ _ _) (wk-β-natrec _ A) $
             wk (lift (lift ρ⊇)) (∙ ⊢A′) ⊢u)
        (natrec-suc {A} {s = u} ⊢t ⊢u ⊢v) PE.refl →
          let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢u
              ⊢A′           = wk (lift ρ⊇) (∙ univ (ℕⱼ ⊢Δ)) ⊢A
                                ⦃ lt = <ˢ-trans A< ! ⦄
          in
          PE.subst₂ (_⊢_≡_∷_ _ _)
            (PE.sym $ wk-β-doubleSubst _ u _ _) (PE.sym $ wk-β A) $
          natrec-suc
            (PE.subst (_⊢_∷_ _ _) (wk-β A) $
             wk ρ⊇ ⊢Δ ⊢t)
            (PE.subst (_⊢_∷_ _ _) (wk-β-natrec _ A) $
             wk (lift (lift ρ⊇)) (∙ ⊢A′) ⊢u)
            (wk ρ⊇ ⊢Δ ⊢v)
        (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) PE.refl →
          Id-cong (wk ρ⊇ ⊢Δ A₁≡A₂) (wk ρ⊇ ⊢Δ t₁≡t₂)
            (wk ρ⊇ ⊢Δ u₁≡u₂)
        (J-cong {B₁} A₁≡A₂ ⊢t₁ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ w₁≡w₂) PE.refl →
          let _ , (⊢A₁ , A₁<) , _ = ∙∙⊢→⊢-<ˢ B₁≡B₂
              ⊢A₁′                = wk ρ⊇ ⊢Δ ⊢A₁ ⦃ lt = <ˢ-trans A₁< ! ⦄
          in
          PE.subst (_⊢_≡_∷_ _ _ _)
            (PE.sym $ wk-β-doubleSubst _ B₁ _ _) $
          J-cong (wk ρ⊇ ⊢Δ A₁≡A₂) (wk ρ⊇ ⊢Δ ⊢t₁)
            (wk ρ⊇ ⊢Δ t₁≡t₂)
            (PE.subst₂ (λ A t → _ » _ ∙ U.wk _ _ ∙ Id A t _ ⊢ _ ≡ _)
               (PE.sym $ wk1-wk≡lift-wk1 _ _)
               (PE.sym $ wk1-wk≡lift-wk1 _ _) $
             wk (lift (lift ρ⊇))
               (∙ (Idⱼ
                     (PE.subst (_⊢_ _) (PE.sym $ lift-wk1 _ _) $
                      wk (step ρ⊇) (∙ ⊢A₁′) ⊢A₁
                        ⦃ lt = <ˢ-trans A₁< ! ⦄)
                     (PE.subst₂ (_ » _ ∙ U.wk _ _ ⊢_∷_)
                        (PE.sym $ lift-wk1 _ _)
                        (PE.sym $ lift-wk1 _ _) $
                      wk (step ρ⊇) (∙ ⊢A₁′) ⊢t₁)
                     (PE.subst (_ » _ ∙ U.wk _ _ ⊢ _ ∷_)
                        (wk1-wk≡lift-wk1 _ _) $
                      var₀ ⊢A₁′)))
               B₁≡B₂)
            (PE.subst (_⊢_≡_∷_ _ _ _) (wk-β-doubleSubst _ B₁ _ _) $
             wk ρ⊇ ⊢Δ u₁≡u₂)
            (wk ρ⊇ ⊢Δ v₁≡v₂) (wk ρ⊇ ⊢Δ w₁≡w₂)
        (J-β {B} ⊢t ⊢B ⊢u eq) PE.refl →
          let _ , (⊢A , A<) , _ = ∙∙⊢→⊢-<ˢ ⊢B
              ⊢A′               = wk ρ⊇ ⊢Δ ⊢A ⦃ lt = <ˢ-trans A< ! ⦄
          in
          PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ wk-β-doubleSubst _ B _ _) $
          J-β (wk ρ⊇ ⊢Δ ⊢t)
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
                      wk (step ρ⊇) (∙ ⊢A′) ⊢t)
                     (PE.subst (_⊢_∷_ _ _) (wk1-wk≡lift-wk1 _ _) $
                      var₀ ⊢A′)))
               ⊢B)
            (PE.subst (_⊢_∷_ _ _) (wk-β-doubleSubst _ B _ _) $
             wk ρ⊇ ⊢Δ ⊢u)
            (PE.cong (U.wk _) eq)
        (K-cong {B₁} A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ ok) PE.refl →
          let _ , ⊢Id                       = ∙⊢→⊢-<ˢ B₁≡B₂
              (⊢A₁ , A₁<) , (⊢t₁ , t₁<) , _ = inversion-Id-⊢-<ˢ ⊢Id
              ⊢A₁′                          = wk ρ⊇ ⊢Δ ⊢A₁
                                                ⦃ lt = <ˢ-trans A₁< ! ⦄
              ⊢t₁′                          = wk ρ⊇ ⊢Δ ⊢t₁
                                                ⦃ lt = <ˢ-trans t₁< ! ⦄
          in
          PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ wk-β B₁) $
          K-cong (wk ρ⊇ ⊢Δ A₁≡A₂) (wk ρ⊇ ⊢Δ t₁≡t₂)
            (wk (lift ρ⊇) (∙ Idⱼ ⊢A₁′ ⊢t₁′ ⊢t₁′) B₁≡B₂)
            (PE.subst (_⊢_≡_∷_ _ _ _) (wk-β B₁) $
             wk ρ⊇ ⊢Δ u₁≡u₂)
            (wk ρ⊇ ⊢Δ v₁≡v₂) ok
        (K-β {B} ⊢B ⊢u ok) PE.refl →
          let _ , ⊢Id                   = ∙⊢→⊢-<ˢ ⊢B
              (⊢A , A<) , (⊢t , t<) , _ = inversion-Id-⊢-<ˢ ⊢Id
              ⊢A′                       = wk ρ⊇ ⊢Δ ⊢A
                                            ⦃ lt = <ˢ-trans A< ! ⦄
              ⊢t′                       = wk ρ⊇ ⊢Δ ⊢t
                                            ⦃ lt = <ˢ-trans t< ! ⦄
          in
          PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ wk-β B) $
          K-β (wk (lift ρ⊇) (∙ Idⱼ ⊢A′ ⊢t′ ⊢t′) ⊢B)
            (PE.subst (_⊢_∷_ _ _) (wk-β B) $
             wk ρ⊇ ⊢Δ ⊢u)
            ok
        ([]-cong-cong l₁≡l₂ A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ ok) PE.refl →
          PE.subst (_⊢_≡_∷_ _ _ _) (wk-Id-Erased _) $
          []-cong-cong (wk ρ⊇ ⊢Δ l₁≡l₂) (wk ρ⊇ ⊢Δ A₁≡A₂)
            (wk ρ⊇ ⊢Δ t₁≡t₂) (wk ρ⊇ ⊢Δ u₁≡u₂) (wk ρ⊇ ⊢Δ v₁≡v₂) ok
        ([]-cong-β ⊢l ⊢t eq ok) PE.refl →
          PE.subst (_⊢_≡_∷_ _ _ _) (wk-Id-Erased _) $
          []-cong-β (wk ρ⊇ ⊢Δ ⊢l) (wk ρ⊇ ⊢Δ ⊢t) (PE.cong (U.wk _) eq) ok
        (equality-reflection ok ⊢Id ⊢v) PE.refl →
          equality-reflection ok (wk ρ⊇ ⊢Δ ⊢Id) (wk ρ⊇ ⊢Δ ⊢v)
        (Quot-cong ok ⊢l A₁≡A₂ B₁≡B₂) PE.refl →
          Quot-cong ok (wk ρ⊇ ⊢Δ ⊢l) (wk ρ⊇ ⊢Δ A₁≡A₂)
            (PE.subst (_⊢_≡_∷_ _ _ _) (wk⇑[]-wk[]≡ 2) $
             wk-Quot-rel-Con-⊢ ρ⊇ ⊢Δ B₁≡B₂)
        (class-cong ⊢Q t₁≡t₂) PE.refl →
          class-cong (wk ρ⊇ ⊢Δ ⊢Q) (wk ρ⊇ ⊢Δ t₁≡t₂)
        (resp-cong {B₁} ok A₁≡A₂ B₁≡B₂ t₁≡t₂ u₁≡u₂ v₁≡v₂) PE.refl →
          resp-cong ok (wk ρ⊇ ⊢Δ A₁≡A₂) (wk-Quot-rel-Con-⊢ ρ⊇ ⊢Δ B₁≡B₂)
            (wk ρ⊇ ⊢Δ t₁≡t₂) (wk ρ⊇ ⊢Δ u₁≡u₂)
            (PE.subst (_⊢_≡_∷_ _ _ _) (wk-β-doubleSubst _ B₁ _ _) $
             wk ρ⊇ ⊢Δ v₁≡v₂)
        (set-cong A₁≡A₂ B₁≡B₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ w₁≡w₂) PE.refl →
          set-cong (wk ρ⊇ ⊢Δ A₁≡A₂) (wk-Quot-rel-Con-⊢ ρ⊇ ⊢Δ B₁≡B₂)
            (wk ρ⊇ ⊢Δ t₁≡t₂) (wk ρ⊇ ⊢Δ u₁≡u₂) (wk ρ⊇ ⊢Δ v₁≡v₂)
            (wk ρ⊇ ⊢Δ w₁≡w₂)
        ⊢q@(qrec-cong {C₁} C₁≡C₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ w₁≡w₂) PE.refl →
          let _ , (⊢A₁ , A₁<) , (⊢B₁ , B₁<) , (⊢C₁ , C₁<) , (⊢Q , Q<) =
                inversion-Is-set-Cons v₁≡v₂

              instance
                _ : size ⊢Q <ˢ size ⊢q
                _ = <ˢ-trans Q< !

                _ : size ⊢A₁ <ˢ size ⊢q
                _ = <ˢ-trans A₁< !

                _ : size ⊢C₁ <ˢ size ⊢q
                _ = <ˢ-trans C₁< !

                _ : size ⊢B₁ <ˢ size ⊢q
                _ = <ˢ-trans B₁< !
          in
          PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym (wk-β C₁)) $
          qrec-cong
            (wk (lift ρ⊇) (∙ wk ρ⊇ ⊢Δ ⊢Q) C₁≡C₂)
            (PE.subst (_⊢_≡_∷_ _ _ _) (wk-β↑ C₁) $
             wk (lift ρ⊇) (∙ wk ρ⊇ ⊢Δ ⊢A₁) t₁≡t₂)
            (PE.subst (_⊢_≡_∷_ _ _ _) wk-Resp-type $
             wk (lift-Resp-Con ρ⊇) (wk-Resp-Con ρ⊇ ⊢Δ ⊢B₁) u₁≡u₂)
            (PE.subst (_⊢_≡_∷_ _ _ _) wk-Is-set-type $
             wk (lift-Is-set-Con ρ⊇) (wk-Is-set-Con ρ⊇ ⊢Δ ⊢C₁)
               v₁≡v₂)
            (wk ρ⊇ ⊢Δ w₁≡w₂)
        ⊢q@(qrec-β {C} {t} ⊢C ⊢t ⊢u ⊢v ⊢w) PE.refl →
          let _ , (⊢A , A<) , (⊢B , B<) , _ , (⊢Q , Q<) =
                inversion-Is-set-Cons ⊢v

              instance
                _ : size ⊢Q <ˢ size ⊢q
                _ = <ˢ-trans Q< !

                _ : size ⊢A <ˢ size ⊢q
                _ = <ˢ-trans A< !

                _ : size ⊢B <ˢ size ⊢q
                _ = <ˢ-trans B< !
          in
          PE.subst₂ (_⊢_≡_∷_ _ _) (PE.sym (wk-β t)) (PE.sym (wk-β C)) $
          qrec-β (wk (lift ρ⊇) (∙ wk ρ⊇ ⊢Δ ⊢Q) ⊢C)
            (PE.subst (_⊢_∷_ _ _) (wk-β↑ C) $
             wk (lift ρ⊇) (∙ wk ρ⊇ ⊢Δ ⊢A) ⊢t)
            (PE.subst (_⊢_∷_ _ _) wk-Resp-type $
             wk (lift-Resp-Con ρ⊇) (wk-Resp-Con ρ⊇ ⊢Δ ⊢B) ⊢u)
            (PE.subst (_⊢_∷_ _ _) wk-Is-set-type $
             wk (lift-Is-set-Con ρ⊇) (wk-Is-set-Con ρ⊇ ⊢Δ ⊢C) ⊢v)
            (wk ρ⊇ ⊢Δ ⊢w)
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
          term ok (wk ρ⊇ ⊢Δ l₁≡l₂)
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
  wk (ρ⊇ , ⊢Δ) ⊢𝓙 =
    Variants.wk (λ _ → Inhabited.P-inhabited) ρ⊇ ⊢Δ ⊢𝓙
      ⦃ lt = ∃-<ˢ .proj₂ ⦄

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

opaque
  unfolding _»_∷ʷ_⊇_

  -- A weakening lemma related to Quot-rel-Con.

  liftʷ-Quot-rel-Con :
    ∇ » ρ ∷ʷ Δ ⊇ Γ →
    ∇ » Γ ⊢ A →
    ∇ » liftn ρ 2 ∷ʷ Quot-rel-Con Δ (U.wk ρ A) ⊇ Quot-rel-Con Γ A
  liftʷ-Quot-rel-Con (ρ⊇ , ⊢Δ) ⊢A =
    lift-Quot-rel-Con ρ⊇ ,
    Variants.wk-Quot-rel-Con (λ _ → Inhabited.P-inhabited) ρ⊇ ⊢Δ ⊢A
      ⦃ lt = ∃-<ˢ .proj₂ ⦄

opaque
  unfolding Quot-rel-Con _»_∷ʷ_⊇_

  -- A weakening lemma related to Resp-Con.

  liftʷ-Resp-Con :
    ∇ » ρ ∷ʷ Δ ⊇ Γ →
    ∇ » Quot-rel-Con Γ A ⊢ B →
    ∇ » liftn ρ 3 ∷ʷ Resp-Con Δ (U.wk ρ A) (U.wk (liftn ρ 2) B) ⊇
      Resp-Con Γ A B
  liftʷ-Resp-Con (ρ⊇ , ⊢Δ) ⊢B =
    lift-Resp-Con ρ⊇ ,
    Variants.wk-Resp-Con (λ _ → Inhabited.P-inhabited) ρ⊇ ⊢Δ ⊢B
      ⦃ lt = ∃-<ˢ .proj₂ ⦄

opaque
  unfolding _»_∷ʷ_⊇_

  -- A weakening lemma related to Is-set-Con.

  liftʷ-Is-set-Con :
    ∇ » ρ ∷ʷ Δ ⊇ Γ →
    ∇ » Γ ∙ Quot A B ⊢ C →
    ∇ » liftn ρ 5 ∷ʷ
      Is-set-Con Δ (U.wk ρ A) (U.wk (liftn ρ 2) B) (U.wk (lift ρ) C) ⊇
      Is-set-Con Γ A B C
  liftʷ-Is-set-Con (ρ⊇ , ⊢Δ) ⊢C =
    lift-Is-set-Con ρ⊇ ,
    Variants.wk-Is-set-Con (λ _ → Inhabited.P-inhabited) ρ⊇ ⊢Δ ⊢C
      ⦃ lt = ∃-<ˢ .proj₂ ⦄

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
  wkRedTerm {ρ} {Δ} [ρ] (prodrec-subst {A} ⊢A ⊢u t⇒t′) =
    let _ , _ , ok = inversion-ΠΣ (⊢∙→⊢ (wf ⊢A))
        ⊢G = ⊢∙→⊢ (wf ⊢u)
        ρF = wk [ρ] (⊢∙→⊢ (wf ⊢G))
        ρG = wk (liftʷʷ [ρ] ρF) ⊢G
        ρA = wk (liftʷʷ [ρ] (ΠΣⱼ ρG ok)) ⊢A
        ρt⇒t′ = wkRedTerm [ρ] t⇒t′
        ρu = wk (liftʷ (lift (∷ʷ⊇→∷⊇ [ρ])) ρG) ⊢u
    in  PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym (wk-β A))
                 (prodrec-subst ρA
                               (PE.subst (λ x → _ ⊢ _ ∷ x)
                                         (wk-β-prodrec ρ A) ρu)
                               ρt⇒t′)
  wkRedTerm {ρ} {Δ} [ρ] (prodrec-β {G} {A} {u} ⊢A ⊢t ⊢t′ ⊢u p≡p′) =
    let _ , _ , ok = inversion-ΠΣ (⊢∙→⊢ (wf ⊢A))
        ⊢G = ⊢∙→⊢ (wf ⊢u)
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
             p≡p′)
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
  wkRedTerm [ρ] (unitrec-subst {A} ⊢A ⊢u t⇒t′ ok) =
    let Unit-ok = inversion-Unit (⊢∙→⊢ (wf ⊢A))
        ρA = wk (liftʷʷ [ρ] (univ (Unitⱼ (wf-∷ʷ⊇ [ρ]) Unit-ok))) ⊢A
        ρu = wk [ρ] ⊢u
        ρu′ = PE.subst (λ x → _ ⊢ _ ∷ x) (wk-β A) ρu
        ρt⇒t′ = wkRedTerm [ρ] t⇒t′
    in  PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym (wk-β A))
          (unitrec-subst ρA ρu′ ρt⇒t′ ok)
  wkRedTerm [ρ] (unitrec-β {A} ⊢A ⊢u ok) =
    let Unit-ok = inversion-Unit (⊢∙→⊢ (wf ⊢A))
        ρA = wk (liftʷʷ [ρ] (univ (Unitⱼ (wf-∷ʷ⊇ [ρ]) Unit-ok))) ⊢A
        ρu = wk [ρ] ⊢u
        ρu′ = PE.subst (λ x → _ ⊢ _ ∷ x) (wk-β A) ρu
    in  PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym (wk-β A))
          (unitrec-β ρA ρu′ ok)
  wkRedTerm ρ (unitrec-β-η {A} ⊢A ⊢t ⊢u ok) =
    let Unit-ok = inversion-Unit (⊢∙→⊢ (wf ⊢A)) in
    PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym (wk-β A)) $
    unitrec-β-η (wk (liftʷʷ ρ (univ (Unitⱼ (wf-∷ʷ⊇ ρ) Unit-ok))) ⊢A)
      (wk ρ ⊢t) (PE.subst (_⊢_∷_ _ _) (wk-β A) (wk ρ ⊢u)) ok
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
  wkRedTerm ρ (resp-η {B} ok ⊢Q ⊢t ⊢u ⊢v) =
    resp-η ok (wk ρ ⊢Q) (wk ρ ⊢t) (wk ρ ⊢u)
      (PE.subst (_⊢_∷_ _ _) (wk-β-doubleSubst _ B _ _) $
       wk ρ ⊢v)
  wkRedTerm ρ (set-η ok ⊢t ⊢u ⊢v ⊢w) =
    set-η ok (wk ρ ⊢t) (wk ρ ⊢u) (wk ρ ⊢v) (wk ρ ⊢w)
  wkRedTerm ρ (qrec-subst {C} ⊢C ⊢t ⊢u ⊢v w₁⇒w₂) =
    let _ , (⊢A , _) , (⊢B , _) , _ , (⊢Q , _) =
          inversion-Is-set-Cons ⊢v
    in
    PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym (wk-β C)) $
    qrec-subst (wk (liftʷʷ ρ (wk ρ ⊢Q)) ⊢C)
      (PE.subst (_⊢_∷_ _ _) (wk-β↑ C) $
       wk (liftʷʷ ρ (wk ρ ⊢A)) ⊢t)
      (PE.subst (_⊢_∷_ _ _) wk-Resp-type $
       wk (liftʷ-Resp-Con ρ ⊢B) ⊢u)
      (PE.subst (_⊢_∷_ _ _) wk-Is-set-type $
       wk (liftʷ-Is-set-Con ρ ⊢C) ⊢v)
      (wkRedTerm ρ w₁⇒w₂)
  wkRedTerm ρ (qrec-β {C} {t} ⊢C ⊢t ⊢u ⊢v ⊢w) =
    let _ , (⊢A , _) , (⊢B , _) , _ , (⊢Q , _) =
          inversion-Is-set-Cons ⊢v
    in
    PE.subst₂ (_⊢_⇒_∷_ _ _) (PE.sym (wk-β t)) (PE.sym (wk-β C)) $
    qrec-β (wk (liftʷʷ ρ (wk ρ ⊢Q)) ⊢C)
      (PE.subst (_⊢_∷_ _ _) (wk-β↑ C) $
       wk (liftʷʷ ρ (wk ρ ⊢A)) ⊢t)
      (PE.subst (_⊢_∷_ _ _) wk-Resp-type $
       wk (liftʷ-Resp-Con ρ ⊢B) ⊢u)
      (PE.subst (_⊢_∷_ _ _) wk-Is-set-type $
       wk (liftʷ-Is-set-Con ρ ⊢C) ⊢v)
      (wk ρ ⊢w)

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
