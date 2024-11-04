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
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M
open import Definition.Typed R hiding (_,_)
open import Definition.Typed.Properties.Admissible.Primitive R
open import Definition.Typed.Properties.Inversion R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Size R

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
open import Tools.Size
open import Tools.Size.Instances

private
  variable
    k ℓ n m : Nat
    s s₂ : Size
    A A₁ A₂ B C t t₁ t₂ u : Term n
    Γ  : Con Term n
    Δ  : Con Term m
    Δ′ : Con Term ℓ
    ρ  : Wk m n
    ρ′ : Wk n ℓ

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

  -- The weakening stepn id k is a well-formed weakening from drop k Δ
  -- to Δ.

  ⊇-drop : stepn id k ∷ Δ ⊇ drop k Δ
  ⊇-drop {k = 0}                = id
  ⊇-drop {k = 1+ _} {Δ = _ ∙ _} = step ⊇-drop

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
        ρ ∷ Δ ⊇ Γ → ⊢ Δ →
        (⊢A : Γ ⊢ A) →
        size-⊢ ⊢A PE.≡ s →
        Δ ⊢ U.wk ρ A
      wkTerm :
        ρ ∷ Δ ⊇ Γ → ⊢ Δ →
        (⊢t : Γ ⊢ t ∷ A) →
        size-⊢∷ ⊢t PE.≡ s →
        Δ ⊢ U.wk ρ t ∷ U.wk ρ A
      wkEq :
        ρ ∷ Δ ⊇ Γ → ⊢ Δ →
        (A≡B : Γ ⊢ A ≡ B) →
        size-⊢≡ A≡B PE.≡ s →
        Δ ⊢ U.wk ρ A ≡ U.wk ρ B
      wkEqTerm :
        ρ ∷ Δ ⊇ Γ → ⊢ Δ →
        (t≡u : Γ ⊢ t ≡ u ∷ A) →
        size-⊢≡∷ t≡u PE.≡ s →
        Δ ⊢ U.wk ρ t ≡ U.wk ρ u ∷ U.wk ρ A

-- Variants of the fields of P.

private module Variants (hyp : ∀ {s₁} → s₁ <ˢ s₂ → P s₁) where

  opaque

    -- Variants of the fields of P.

    wk :
      ρ ∷ Δ ⊇ Γ → ⊢ Δ →
      (⊢A : Γ ⊢ A)
      ⦃ lt : size-⊢ ⊢A <ˢ s₂ ⦄ →
      Δ ⊢ U.wk ρ A
    wk ρ⊇ ⊢Δ ⊢A ⦃ lt ⦄ = P.wk (hyp lt) ρ⊇ ⊢Δ ⊢A PE.refl

    wkTerm :
      ρ ∷ Δ ⊇ Γ → ⊢ Δ →
      (⊢t : Γ ⊢ t ∷ A)
      ⦃ lt : size-⊢∷ ⊢t <ˢ s₂ ⦄ →
      Δ ⊢ U.wk ρ t ∷ U.wk ρ A
    wkTerm ρ⊇ ⊢Δ ⊢t ⦃ lt ⦄ = P.wkTerm (hyp lt) ρ⊇ ⊢Δ ⊢t PE.refl

    wkEq :
      ρ ∷ Δ ⊇ Γ → ⊢ Δ →
      (A≡B : Γ ⊢ A ≡ B)
      ⦃ lt : size-⊢≡ A≡B <ˢ s₂ ⦄ →
      Δ ⊢ U.wk ρ A ≡ U.wk ρ B
    wkEq ρ⊇ ⊢Δ A≡B ⦃ lt ⦄ = P.wkEq (hyp lt) ρ⊇ ⊢Δ A≡B PE.refl

    wkEqTerm :
      ρ ∷ Δ ⊇ Γ → ⊢ Δ →
      (t≡u : Γ ⊢ t ≡ u ∷ A)
      ⦃ lt : size-⊢≡∷ t≡u <ˢ s₂ ⦄ →
      Δ ⊢ U.wk ρ t ≡ U.wk ρ u ∷ U.wk ρ A
    wkEqTerm ρ⊇ ⊢Δ t≡u ⦃ lt ⦄ = P.wkEqTerm (hyp lt) ρ⊇ ⊢Δ t≡u PE.refl

-- The type P s is inhabited for every s.

private module Inhabited where

  opaque
    unfolding size-⊢

    -- A weakening lemma for _⊢_.

    wk′ :
      (∀ {s₁} → s₁ <ˢ s₂ → P s₁) →
      ρ ∷ Δ ⊇ Γ → ⊢ Δ →
      (⊢A : Γ ⊢ A) →
      size-⊢ ⊢A PE.≡ s₂ →
      Δ ⊢ U.wk ρ A
    wk′ hyp ρ⊇ ⊢Δ = λ where
        (Uⱼ _) _ →
          Uⱼ ⊢Δ
        (univ ⊢A) PE.refl →
          univ (wkTerm ρ⊇ ⊢Δ ⊢A)
        (ΠΣⱼ ⊢B ok) PE.refl →
          let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢B
              ⊢A′           = wk ρ⊇ ⊢Δ ⊢A ⦃ lt = <ˢ-trans A< ! ⦄
          in
          ΠΣⱼ (wk (lift ρ⊇) (∙ ⊢A′) ⊢B) ok
        (Emptyⱼ _) _ →
          Emptyⱼ ⊢Δ
        (Unitⱼ _ ok) _ →
          Unitⱼ ⊢Δ ok
        (ℕⱼ _) _ →
          ℕⱼ ⊢Δ
        (Idⱼ ⊢A ⊢t ⊢u) PE.refl →
          Idⱼ (wk ρ⊇ ⊢Δ ⊢A) (wkTerm ρ⊇ ⊢Δ ⊢t) (wkTerm ρ⊇ ⊢Δ ⊢u)
      where
      open Variants hyp

  opaque
    unfolding size-⊢∷

    -- A weakening lemma for _⊢_∷_.

    wkTerm′ :
      (∀ {s₁} → s₁ <ˢ s₂ → P s₁) →
      ρ ∷ Δ ⊇ Γ → ⊢ Δ →
      (⊢t : Γ ⊢ t ∷ A) →
      size-⊢∷ ⊢t PE.≡ s₂ →
      Δ ⊢ U.wk ρ t ∷ U.wk ρ A
    wkTerm′ hyp ρ⊇ ⊢Δ = λ where
        (conv ⊢t B≡A) PE.refl →
          conv (wkTerm ρ⊇ ⊢Δ ⊢t) (wkEq ρ⊇ ⊢Δ B≡A)
        (var _ x∈) _ →
          var ⊢Δ (wkIndex ρ⊇ x∈)
        (Uⱼ _) _ →
          Uⱼ ⊢Δ
        (ΠΣⱼ ⊢A ⊢B ok) PE.refl →
          let ⊢A′ = wkTerm ρ⊇ ⊢Δ ⊢A in
          ΠΣⱼ ⊢A′ (wkTerm (lift ρ⊇) (∙ univ ⊢A′) ⊢B) ok
        (lamⱼ ⊢B ⊢t ok) PE.refl →
          let _ , (⊢A , A<) = ∙⊢∷→⊢-<ˢ ⊢t
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
          let _ , (⊢A , A<) , (⊢B , B<) = ∙∙⊢∷→⊢-<ˢ ⊢u
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
        (starⱼ _ ok) _ →
          starⱼ ⊢Δ ok
        (unitrecⱼ {A} ⊢A ⊢t ⊢u ok) PE.refl →
          PE.subst (_⊢_∷_ _ _) (PE.sym $ wk-β A) $
          unitrecⱼ (wk (lift ρ⊇) (∙ Unitⱼ ⊢Δ ok) ⊢A) (wkTerm ρ⊇ ⊢Δ ⊢t)
            (PE.subst (_⊢_∷_ _ _) (wk-β A) $
             wkTerm ρ⊇ ⊢Δ ⊢u)
            ok
        (Unitⱼ _ ok) _ →
          Unitⱼ ⊢Δ ok
        (ℕⱼ _) _ →
          ℕⱼ ⊢Δ
        (zeroⱼ _) _ →
          zeroⱼ ⊢Δ
        (sucⱼ ⊢t) PE.refl →
          sucⱼ (wkTerm ρ⊇ ⊢Δ ⊢t)
        (natrecⱼ {A} ⊢t ⊢u ⊢v) PE.refl →
          let _ , (⊢A , A<) = ∙⊢∷→⊢-<ˢ ⊢u
              ⊢A′           = wk (lift ρ⊇) (∙ ℕⱼ ⊢Δ) ⊢A
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
            (PE.subst₂ (λ A t → _ ∙ U.wk _ _ ∙ Id A t _ ⊢ _)
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
        (Kⱼ {B} ⊢t ⊢B ⊢u ⊢v ok) PE.refl →
          let _ , (⊢Id , Id<) = ∙⊢→⊢-<ˢ ⊢B
              (⊢A , A<) , _   = inversion-Id-⊢ ⊢Id
              ⊢A′             = wk ρ⊇ ⊢Δ ⊢A
                                  ⦃ lt = <ˢ-trans (<ˢ-trans A< Id<) ! ⦄
              ⊢t′             = wkTerm ρ⊇ ⊢Δ ⊢t
          in
          PE.subst (_⊢_∷_ _ _) (PE.sym $ wk-β B) $
          Kⱼ ⊢t′ (wk (lift ρ⊇) (∙ Idⱼ ⊢A′ ⊢t′ ⊢t′) ⊢B)
            (PE.subst (_⊢_∷_ _ _) (wk-β B) $
             wkTerm ρ⊇ ⊢Δ ⊢u)
            (wkTerm ρ⊇ ⊢Δ ⊢v) ok
        ([]-congⱼ ⊢A ⊢t ⊢u ⊢v ok) PE.refl →
          []-congⱼ (wk ρ⊇ ⊢Δ ⊢A) (wkTerm ρ⊇ ⊢Δ ⊢t) (wkTerm ρ⊇ ⊢Δ ⊢u)
            (wkTerm ρ⊇ ⊢Δ ⊢v) ok
      where
      open Variants hyp

  opaque
    unfolding size-⊢≡

    -- A weakening lemma for _⊢_≡_.

    wkEq′ :
      (∀ {s₁} → s₁ <ˢ s₂ → P s₁) →
      ρ ∷ Δ ⊇ Γ → ⊢ Δ →
      (A₁≡A₂ : Γ ⊢ A₁ ≡ A₂) →
      size-⊢≡ A₁≡A₂ PE.≡ s₂ →
      Δ ⊢ U.wk ρ A₁ ≡ U.wk ρ A₂
    wkEq′ hyp ρ⊇ ⊢Δ = λ where
        (univ A₁≡A₂) PE.refl →
          univ (wkEqTerm ρ⊇ ⊢Δ A₁≡A₂)
        (refl ⊢A) PE.refl →
          refl (wk ρ⊇ ⊢Δ ⊢A)
        (sym A₂≡A₁) PE.refl →
          sym (wkEq ρ⊇ ⊢Δ A₂≡A₁)
        (trans A₁≡A₂ A₂≡A₃) PE.refl →
          trans (wkEq ρ⊇ ⊢Δ A₁≡A₂) (wkEq ρ⊇ ⊢Δ A₂≡A₃)
        (ΠΣ-cong A₁≡A₂ B₁≡B₂ ok) PE.refl →
          let _ , (⊢A₁ , A₁<) = ∙⊢≡→⊢-<ˢ B₁≡B₂
              ⊢A₁′            = wk ρ⊇ ⊢Δ ⊢A₁ ⦃ lt = <ˢ-trans A₁< ! ⦄
          in
          ΠΣ-cong (wkEq ρ⊇ ⊢Δ A₁≡A₂) (wkEq (lift ρ⊇) (∙ ⊢A₁′) B₁≡B₂) ok
        (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) PE.refl →
          Id-cong (wkEq ρ⊇ ⊢Δ A₁≡A₂) (wkEqTerm ρ⊇ ⊢Δ t₁≡t₂)
            (wkEqTerm ρ⊇ ⊢Δ u₁≡u₂)
      where
      open Variants hyp

  opaque
    unfolding size-⊢≡∷

    -- A weakening lemma for _⊢_≡_∷_.

    wkEqTerm′ :
      (∀ {s₁} → s₁ <ˢ s₂ → P s₁) →
      ρ ∷ Δ ⊇ Γ → ⊢ Δ →
      (t₁≡t₂ : Γ ⊢ t₁ ≡ t₂ ∷ A) →
      size-⊢≡∷ t₁≡t₂ PE.≡ s₂ →
      Δ ⊢ U.wk ρ t₁ ≡ U.wk ρ t₂ ∷ U.wk ρ A
    wkEqTerm′ hyp ρ⊇ ⊢Δ = λ where
        (refl ⊢t) PE.refl →
          refl (wkTerm ρ⊇ ⊢Δ ⊢t)
        (sym ⊢A t₂≡t₁) PE.refl →
          sym (wk ρ⊇ ⊢Δ ⊢A) (wkEqTerm ρ⊇ ⊢Δ t₂≡t₁)
        (trans t₁≡t₂ t₂≡t₃) PE.refl →
          trans (wkEqTerm ρ⊇ ⊢Δ t₁≡t₂) (wkEqTerm ρ⊇ ⊢Δ t₂≡t₃)
        (conv t₁≡t₂ B≡A) PE.refl →
          conv (wkEqTerm ρ⊇ ⊢Δ t₁≡t₂) (wkEq ρ⊇ ⊢Δ B≡A)
        (ΠΣ-cong A₁≡A₂ B₁≡B₂ ok) PE.refl →
          let _ , (⊢A₁ , A₁<) = ∙⊢≡∷→⊢-<ˢ B₁≡B₂
              ⊢A₁′            = wk ρ⊇ ⊢Δ ⊢A₁ ⦃ lt = <ˢ-trans A₁< ! ⦄
          in
          ΠΣ-cong (wkEqTerm ρ⊇ ⊢Δ A₁≡A₂)
            (wkEqTerm (lift ρ⊇) (∙ ⊢A₁′) B₁≡B₂) ok
        (app-cong {G = B} t₁≡t₂ u₁≡u₂) PE.refl →
          PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ wk-β B) $
          app-cong (wkEqTerm ρ⊇ ⊢Δ t₁≡t₂) (wkEqTerm ρ⊇ ⊢Δ u₁≡u₂)
        (β-red {G = B} {t} ⊢B ⊢t ⊢u eq ok) PE.refl →
          let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢B
              ⊢A′           = wk ρ⊇ ⊢Δ ⊢A ⦃ lt = <ˢ-trans A< ! ⦄
          in
          PE.subst₂ (_⊢_≡_∷_ _ _) (PE.sym $ wk-β t) (PE.sym $ wk-β B) $
          β-red (wk (lift ρ⊇) (∙ ⊢A′) ⊢B) (wkTerm (lift ρ⊇) (∙ ⊢A′) ⊢t)
            (wkTerm ρ⊇ ⊢Δ ⊢u) eq ok
        (η-eq {f = t₁} {g = t₂} ⊢B ⊢t₁ ⊢t₂ t₁0≡t₂0 ok) PE.refl →
          let _ , (⊢A , A<) = ∙⊢≡∷→⊢-<ˢ t₁0≡t₂0
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
          let _ , (⊢A , A<) , (⊢B , B<) = ∙∙⊢≡∷→⊢-<ˢ u₁≡u₂
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
          let _ , (⊢A , A<) , (⊢B , B<) = ∙∙⊢∷→⊢-<ˢ ⊢v
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
            (wkEq (lift ρ⊇) (∙ Unitⱼ ⊢Δ ok) A₁≡A₂)
            (wkEqTerm ρ⊇ ⊢Δ t₁≡t₂)
            (PE.subst (_⊢_≡_∷_ _ _ _) (wk-β A₁) $
             wkEqTerm ρ⊇ ⊢Δ u₁≡u₂)
            ok no-η
        (unitrec-β {A} ⊢A ⊢t ok no-η) PE.refl →
          PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ wk-β A) $
          unitrec-β (wk (lift ρ⊇) (∙ Unitⱼ ⊢Δ ok) ⊢A)
            (PE.subst (_⊢_∷_ _ _) (wk-β A) $
             wkTerm ρ⊇ ⊢Δ ⊢t)
            ok no-η
        (unitrec-β-η {A} ⊢A ⊢t ⊢u ok η) PE.refl →
          PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ wk-β A) $
          unitrec-β-η (wk (lift ρ⊇) (∙ Unitⱼ ⊢Δ ok) ⊢A)
            (wkTerm ρ⊇ ⊢Δ ⊢t)
            (PE.subst (_⊢_∷_ _ _) (wk-β A) $
             wkTerm ρ⊇ ⊢Δ ⊢u)
            ok η
        (η-unit ⊢t₁ ⊢t₂ η) PE.refl →
          η-unit (wkTerm ρ⊇ ⊢Δ ⊢t₁) (wkTerm ρ⊇ ⊢Δ ⊢t₂) η
        (suc-cong t₁≡t₂) PE.refl →
          suc-cong (wkEqTerm ρ⊇ ⊢Δ t₁≡t₂)
        (natrec-cong {A = A₁} A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂) PE.refl →
          let _ , (⊢A₁ , A₁<) = ∙⊢≡∷→⊢-<ˢ u₁≡u₂
              ⊢A₁′            = wk (lift ρ⊇) (∙ ℕⱼ ⊢Δ) ⊢A₁
                                  ⦃ lt = <ˢ-trans A₁< ! ⦄
          in
          PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ wk-β A₁) $
          natrec-cong (wkEq (lift ρ⊇) (∙ ℕⱼ ⊢Δ) A₁≡A₂)
            (PE.subst (_⊢_≡_∷_ _ _ _) (wk-β A₁) $
             wkEqTerm ρ⊇ ⊢Δ t₁≡t₂)
            (PE.subst (_⊢_≡_∷_ _ _ _) (wk-β-natrec _ A₁) $
             wkEqTerm (lift (lift ρ⊇)) (∙ ⊢A₁′) u₁≡u₂)
            (wkEqTerm ρ⊇ ⊢Δ v₁≡v₂)
        (natrec-zero {A} ⊢t ⊢u) PE.refl →
          let _ , (⊢A , A<) = ∙⊢∷→⊢-<ˢ ⊢u
              ⊢A′           = wk (lift ρ⊇) (∙ ℕⱼ ⊢Δ) ⊢A
                                ⦃ lt = <ˢ-trans A< ! ⦄
          in
          PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ wk-β A) $
          natrec-zero
            (PE.subst (_⊢_∷_ _ _) (wk-β A) $
             wkTerm ρ⊇ ⊢Δ ⊢t)
            (PE.subst (_⊢_∷_ _ _) (wk-β-natrec _ A) $
             wkTerm (lift (lift ρ⊇)) (∙ ⊢A′) ⊢u)
        (natrec-suc {A} {s = u} ⊢t ⊢u ⊢v) PE.refl →
          let _ , (⊢A , A<) = ∙⊢∷→⊢-<ˢ ⊢u
              ⊢A′           = wk (lift ρ⊇) (∙ ℕⱼ ⊢Δ) ⊢A
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
          let _ , (⊢A₁ , A₁<) , _ = ∙∙⊢≡→⊢-<ˢ B₁≡B₂
              ⊢A₁′                = wk ρ⊇ ⊢Δ ⊢A₁ ⦃ lt = <ˢ-trans A₁< ! ⦄
          in
          PE.subst (_⊢_≡_∷_ _ _ _)
            (PE.sym $ wk-β-doubleSubst _ B₁ _ _) $
          J-cong (wkEq ρ⊇ ⊢Δ A₁≡A₂) (wkTerm ρ⊇ ⊢Δ ⊢t₁)
            (wkEqTerm ρ⊇ ⊢Δ t₁≡t₂)
            (PE.subst₂ (λ A t → _ ∙ U.wk _ _ ∙ Id A t _ ⊢ _ ≡ _)
               (PE.sym $ wk1-wk≡lift-wk1 _ _)
               (PE.sym $ wk1-wk≡lift-wk1 _ _) $
             wkEq (lift (lift ρ⊇))
               (∙ (Idⱼ
                     (PE.subst (_⊢_ _) (PE.sym $ lift-wk1 _ _) $
                      wk (step ρ⊇) (∙ ⊢A₁′) ⊢A₁
                        ⦃ lt = <ˢ-trans A₁< ! ⦄)
                     (PE.subst₂ (_ ∙ U.wk _ _ ⊢_∷_)
                        (PE.sym $ lift-wk1 _ _)
                        (PE.sym $ lift-wk1 _ _) $
                      wkTerm (step ρ⊇) (∙ ⊢A₁′) ⊢t₁)
                     (PE.subst (_ ∙ U.wk _ _ ⊢ _ ∷_)
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
            (PE.subst₂ (λ A t → _ ∙ U.wk _ _ ∙ Id A t _ ⊢ _)
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
        (K-cong {B₁} A₁≡A₂ ⊢t₁ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ ok) PE.refl →
          let _ , (⊢Id , Id<) = ∙⊢≡→⊢-<ˢ B₁≡B₂
              (⊢A₁ , A₁<) , _ = inversion-Id-⊢ ⊢Id
              ⊢A₁′            = wk ρ⊇ ⊢Δ ⊢A₁
                                  ⦃ lt = <ˢ-trans (<ˢ-trans A₁< Id<) ! ⦄
              ⊢t₁′            = wkTerm ρ⊇ ⊢Δ ⊢t₁
          in
          PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ wk-β B₁) $
          K-cong (wkEq ρ⊇ ⊢Δ A₁≡A₂) ⊢t₁′
            (wkEqTerm ρ⊇ ⊢Δ t₁≡t₂)
            (wkEq (lift ρ⊇) (∙ Idⱼ ⊢A₁′ ⊢t₁′ ⊢t₁′) B₁≡B₂)
            (PE.subst (_⊢_≡_∷_ _ _ _) (wk-β B₁) $
             wkEqTerm ρ⊇ ⊢Δ u₁≡u₂)
            (wkEqTerm ρ⊇ ⊢Δ v₁≡v₂) ok
        (K-β {B} ⊢t ⊢B ⊢u ok) PE.refl →
          let _ , (⊢Id , Id<) = ∙⊢→⊢-<ˢ ⊢B
              (⊢A , A<) , _   = inversion-Id-⊢ ⊢Id
              ⊢A′             = wk ρ⊇ ⊢Δ ⊢A
                                  ⦃ lt = <ˢ-trans (<ˢ-trans A< Id<) ! ⦄
              ⊢t′             = wkTerm ρ⊇ ⊢Δ ⊢t
          in
          PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ wk-β B) $
          K-β ⊢t′ (wk (lift ρ⊇) (∙ Idⱼ ⊢A′ ⊢t′ ⊢t′) ⊢B)
            (PE.subst (_⊢_∷_ _ _) (wk-β B) $
             wkTerm ρ⊇ ⊢Δ ⊢u)
            ok
        ([]-cong-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ ok) PE.refl →
          []-cong-cong (wkEq ρ⊇ ⊢Δ A₁≡A₂) (wkEqTerm ρ⊇ ⊢Δ t₁≡t₂)
            (wkEqTerm ρ⊇ ⊢Δ u₁≡u₂) (wkEqTerm ρ⊇ ⊢Δ v₁≡v₂) ok
        ([]-cong-β ⊢t eq ok) PE.refl →
          []-cong-β (wkTerm ρ⊇ ⊢Δ ⊢t) (PE.cong (U.wk _) eq) ok
      where
      open Variants hyp

  opaque

    -- The type P s is inhabited for every s.

    P-inhabited : P s
    P-inhabited =
      well-founded-induction P
        (λ _ hyp →
           record
             { wk       = wk′       hyp
             ; wkTerm   = wkTerm′   hyp
             ; wkEq     = wkEq′     hyp
             ; wkEqTerm = wkEqTerm′ hyp
             })
        _

opaque

  -- A weakening lemma for _⊢_.

  wk : ρ ∷ Δ ⊇ Γ → ⊢ Δ → Γ ⊢ A → Δ ⊢ U.wk ρ A
  wk ρ⊇ ⊢Δ ⊢A = P.wk Inhabited.P-inhabited ρ⊇ ⊢Δ ⊢A PE.refl

opaque

  -- A weakening lemma for _⊢_∷_.

  wkTerm : ρ ∷ Δ ⊇ Γ → ⊢ Δ → Γ ⊢ t ∷ A → Δ ⊢ U.wk ρ t ∷ U.wk ρ A
  wkTerm ρ⊇ ⊢Δ ⊢t = P.wkTerm Inhabited.P-inhabited ρ⊇ ⊢Δ ⊢t PE.refl

opaque

  -- A weakening lemma for _⊢_≡_.

  wkEq : ρ ∷ Δ ⊇ Γ → ⊢ Δ → Γ ⊢ A ≡ B → Δ ⊢ U.wk ρ A ≡ U.wk ρ B
  wkEq ρ⊇ ⊢Δ A≡B = P.wkEq Inhabited.P-inhabited ρ⊇ ⊢Δ A≡B PE.refl

opaque

  -- A weakening lemma for _⊢_≡_∷_.

  wkEqTerm :
    ρ ∷ Δ ⊇ Γ → ⊢ Δ → Γ ⊢ t ≡ u ∷ A → Δ ⊢ U.wk ρ t ≡ U.wk ρ u ∷ U.wk ρ A
  wkEqTerm ρ⊇ ⊢Δ t≡u =
    P.wkEqTerm Inhabited.P-inhabited ρ⊇ ⊢Δ t≡u PE.refl

opaque

  -- A special case of wk.

  wk₁ : Γ ⊢ B → Γ ⊢ A → Γ ∙ B ⊢ wk1 A
  wk₁ ⊢B ⊢A = wk (step id) (∙ ⊢B) ⊢A

opaque

  -- A special case of wkEq.

  wkEq₁ : Γ ⊢ C → Γ ⊢ A ≡ B → Γ ∙ C ⊢ wk1 A ≡ wk1 B
  wkEq₁ ⊢C A≡B = wkEq (step id) (∙ ⊢C) A≡B

opaque

  -- A special case of wkTerm.

  wkTerm₁ : Γ ⊢ B → Γ ⊢ t ∷ A → Γ ∙ B ⊢ wk1 t ∷ wk1 A
  wkTerm₁ ⊢B ⊢t = wkTerm (step id) (∙ ⊢B) ⊢t

opaque

  -- A special case of wkEqTerm.

  wkEqTerm₁ : Γ ⊢ B → Γ ⊢ t ≡ u ∷ A → Γ ∙ B ⊢ wk1 t ≡ wk1 u ∷ wk1 A
  wkEqTerm₁ ⊢B t≡u = wkEqTerm (step id) (∙ ⊢B) t≡u

mutual
  wkRed : ρ ∷ Δ ⊇ Γ →
           let ρA = U.wk ρ A
               ρB = U.wk ρ B
           in ⊢ Δ → Γ ⊢ A ⇒ B → Δ ⊢ ρA ⇒ ρB
  wkRed ρ ⊢Δ (univ A⇒B) = univ (wkRedTerm ρ ⊢Δ A⇒B)

  wkRedTerm : {Δ : Con Term m} {ρ : Wk m n} → ρ ∷ Δ ⊇ Γ →
           let ρA = U.wk ρ A
               ρt = U.wk ρ t
               ρu = U.wk ρ u
           in ⊢ Δ → Γ ⊢ t ⇒ u ∷ A → Δ ⊢ ρt ⇒ ρu ∷ ρA
  wkRedTerm ρ ⊢Δ (conv t⇒u A≡B) = conv (wkRedTerm ρ ⊢Δ t⇒u) (wkEq ρ ⊢Δ A≡B)
  wkRedTerm ρ ⊢Δ (app-subst {G = B} t⇒u a) =
    PE.subst (λ x → _ ⊢ _ ⇒ _ ∷ x) (PE.sym (wk-β B))
             (app-subst (wkRedTerm ρ ⊢Δ t⇒u) (wkTerm ρ ⊢Δ a))
  wkRedTerm ρ ⊢Δ (β-red {F = A} {G = B} {t} {a} ⊢B ⊢t ⊢a p≡q ok) =
    let ⊢ρA = wk ρ ⊢Δ (⊢∙→⊢ (wf ⊢B))
        ⊢ρB = wk (lift ρ) (∙ ⊢ρA) ⊢B
    in  PE.subst (λ x → _ ⊢ _ ⇒ _ ∷ x) (PE.sym (wk-β B))
                 (PE.subst (λ x → _ ⊢ U.wk _ (lam _ t ∘ a) ⇒ x ∷ _)
                           (PE.sym (wk-β t))
                           (β-red ⊢ρB (wkTerm (lift ρ) (∙ ⊢ρA) ⊢t)
                              (wkTerm ρ ⊢Δ ⊢a) p≡q ok))
  wkRedTerm ρ ⊢Δ (fst-subst ⊢G t⇒) =
    let ρF = wk ρ ⊢Δ (⊢∙→⊢ (wf ⊢G))
        ρG = wk (lift ρ) (∙ ρF) ⊢G
        ρt⇒ = wkRedTerm ρ ⊢Δ t⇒
    in  fst-subst ρG ρt⇒
  wkRedTerm ρ ⊢Δ (snd-subst {G} ⊢G t⇒) =
    let ρF = wk ρ ⊢Δ (⊢∙→⊢ (wf ⊢G))
        ρG = wk (lift ρ) (∙ ρF) ⊢G
        ρt⇒ = wkRedTerm ρ ⊢Δ t⇒
    in  PE.subst (λ x → _ ⊢ snd _ _ ⇒ snd _ _ ∷ x) (PE.sym (wk-β G))
      (snd-subst ρG ρt⇒)
  wkRedTerm {ρ} [ρ] ⊢Δ (Σ-β₁ {G} ⊢G t u p≡p′ ok) =
    let ρF = wk [ρ] ⊢Δ (⊢∙→⊢ (wf ⊢G))
        ρG = wk (lift [ρ]) (∙ ρF) ⊢G
        ρt = wkTerm [ρ] ⊢Δ t
        ρu = wkTerm [ρ] ⊢Δ u
        ρu = PE.subst (λ x → _ ⊢ _ ∷ x) (wk-β G) ρu
    in  Σ-β₁ ρG ρt ρu p≡p′ ok
  wkRedTerm {ρ} [ρ] ⊢Δ (Σ-β₂ {G} ⊢G t u p≡p′ ok) =
    let ρF = wk [ρ] ⊢Δ (⊢∙→⊢ (wf ⊢G))
        ρG = wk (lift [ρ]) (∙ ρF) ⊢G
        ρt = wkTerm [ρ] ⊢Δ t
        ρu = wkTerm [ρ] ⊢Δ u
        ρu = PE.subst (λ x → _ ⊢ _ ∷ x) (wk-β G) ρu
    in  PE.subst (λ x → _ ⊢ _ ⇒ _ ∷ x) (PE.sym (wk-β G))
      (Σ-β₂ ρG ρt ρu p≡p′ ok)
  wkRedTerm {Δ} {ρ} [ρ] ⊢Δ (prodrec-subst {A} ⊢A ⊢u t⇒t′ ok) =
    let ⊢G = ⊢∙→⊢ (wfTerm ⊢u)
        ρF = wk [ρ] ⊢Δ (⊢∙→⊢ (wf ⊢G))
        ρG = wk (lift [ρ]) (∙ ρF) ⊢G
        ρA = wk (lift [ρ]) (∙ ΠΣⱼ ρG ok) ⊢A
        ρt⇒t′ = wkRedTerm [ρ] ⊢Δ t⇒t′
        ρu = wkTerm (lift (lift [ρ])) (∙ ρG) ⊢u
    in  PE.subst (λ x → Δ ⊢ prodrec _ _ _ _ _ _ ⇒ _ ∷ x) (PE.sym (wk-β A))
                 (prodrec-subst ρA
                               (PE.subst (λ x → _ ⊢ _ ∷ x)
                                         (wk-β-prodrec ρ A) ρu)
                               ρt⇒t′ ok)
  wkRedTerm
    {Δ} {ρ} [ρ] ⊢Δ (prodrec-β {G} {A} {u} ⊢A ⊢t ⊢t′ ⊢u p≡p′ ok) =
    let ⊢G = ⊢∙→⊢ (wfTerm ⊢u)
        ρF = wk [ρ] ⊢Δ (⊢∙→⊢ (wf ⊢G))
        ρG = wk (lift [ρ]) (∙ ρF) ⊢G
        ρA = wk (lift [ρ]) (∙ ΠΣⱼ ρG ok) ⊢A
        ρt = wkTerm [ρ] ⊢Δ ⊢t
        ρt′ = wkTerm [ρ] ⊢Δ ⊢t′
        ρu = wkTerm (lift (lift [ρ])) (∙ ρG) ⊢u
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
  wkRedTerm [ρ] ⊢Δ (natrec-subst {A = F} ⊢z ⊢s n⇒n′) =
    PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym (wk-β F)) $
    natrec-subst (PE.subst (_⊢_∷_ _ _) (wk-β F) (wkTerm [ρ] ⊢Δ ⊢z))
      (PE.subst (_⊢_∷_ _ _) (wk-β-natrec _ F) $
       wkTerm (lift (lift [ρ]))
         (∙ wk (lift [ρ]) (∙ ℕⱼ ⊢Δ) (⊢∙→⊢ (wfTerm ⊢s))) ⊢s)
      (wkRedTerm [ρ] ⊢Δ n⇒n′)
  wkRedTerm [ρ] ⊢Δ (natrec-zero {A = F} ⊢z ⊢s) =
    PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym (wk-β F)) $
    natrec-zero (PE.subst (_⊢_∷_ _ _) (wk-β F) (wkTerm [ρ] ⊢Δ ⊢z))
      (PE.subst (_⊢_∷_ _ _) (wk-β-natrec _ F) $
       wkTerm (lift (lift [ρ]))
         (∙ wk (lift [ρ]) (∙ ℕⱼ ⊢Δ) (⊢∙→⊢ (wfTerm ⊢s))) ⊢s)
  wkRedTerm
    {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ
    (natrec-suc {z} {A = F} {s} {p} {q} {r} {n} ⊢z ⊢s ⊢n) =
    let ρn = wkTerm [ρ] ⊢Δ ⊢n
        ρF = wk (lift [ρ]) (∙ ℕⱼ ⊢Δ) (⊢∙→⊢ (wfTerm ⊢s))
        ρz = PE.subst (λ x → _ ⊢ _ ∷ x) (wk-β F) (wkTerm [ρ] ⊢Δ ⊢z)
        ρs = U.wk ρ (s [ n , natrec p q r F z s n ]₁₀)
    in  PE.subst (λ x → _ ⊢ natrec _ _ _ (U.wk (lift ρ) F) _ _ _ ⇒ ρs ∷ x)
             (PE.sym (wk-β F))
             (PE.subst (λ x → _ ⊢ natrec _ _ _ _ _ _ _ ⇒ x ∷ _)
                       (PE.sym (wk-β-doubleSubst ρ s (natrec p q r F z s n) n))
                       (natrec-suc ρz
                                   (PE.subst (λ x → ((Δ ∙ ℕ) ∙ (U.wk (lift ρ) F)) ⊢ _ ∷ x)
                                             (wk-β-natrec _ F)
                                             (wkTerm (lift (lift [ρ]))
                                                (∙ ρF) ⊢s))
                                   ρn))
  wkRedTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (emptyrec-subst {A = A} ⊢A n⇒n′) =
    (emptyrec-subst (wk [ρ] ⊢Δ ⊢A)
                    (wkRedTerm [ρ] ⊢Δ n⇒n′))
  wkRedTerm {ρ = ρ} [ρ] ⊢Δ (unitrec-subst {A = A} ⊢A ⊢u t⇒t′ ok₁ ok₂) =
    let ρA = wk (lift [ρ]) (∙ Unitⱼ ⊢Δ ok₁) ⊢A
        ρu = wkTerm [ρ] ⊢Δ ⊢u
        ρu′ = PE.subst (λ x → _ ⊢ _ ∷ x) (wk-β A) ρu
        ρt⇒t′ = wkRedTerm [ρ] ⊢Δ t⇒t′
    in  PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym (wk-β A))
          (unitrec-subst ρA ρu′ ρt⇒t′ ok₁ ok₂)
  wkRedTerm {ρ = ρ} [ρ] ⊢Δ (unitrec-β {A = A} ⊢A ⊢u ok₁ ok₂) =
    let ρA = wk (lift [ρ]) (∙ Unitⱼ ⊢Δ ok₁) ⊢A
        ρu = wkTerm [ρ] ⊢Δ ⊢u
        ρu′ = PE.subst (λ x → _ ⊢ _ ∷ x) (wk-β A) ρu
    in  PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym (wk-β A))
          (unitrec-β ρA ρu′ ok₁ ok₂)
  wkRedTerm ρ ⊢Δ (unitrec-β-η {A} ⊢A ⊢t ⊢u ok₁ ok₂) =
    PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym (wk-β A)) $
    unitrec-β-η (wk (lift ρ) (∙ Unitⱼ ⊢Δ ok₁) ⊢A) (wkTerm ρ ⊢Δ ⊢t)
      (PE.subst (_⊢_∷_ _ _) (wk-β A) (wkTerm ρ ⊢Δ ⊢u)) ok₁ ok₂
  wkRedTerm ρ ⊢Δ (J-subst {B} ⊢t ⊢B ⊢u ⊢t′ ⊢v) =
    PE.subst (_ ⊢ U.wk _ (J _ _ _ _ _ _ _ _) ⇒ _ ∷_)
      (PE.sym $ wk-β-doubleSubst _ B _ _) $
    J-subst (wkTerm ρ ⊢Δ ⊢t)
      (PE.subst₂ (λ A t → _ ∙ U.wk _ _ ∙ Id A t _ ⊢ _)
         (PE.sym $ wk1-wk≡lift-wk1 _ _)
         (PE.sym $ wk1-wk≡lift-wk1 _ _) $
       wk (lift (lift ρ))
         (∙ (Idⱼ
               (PE.subst (_⊢_ _) (PE.sym $ lift-wk1 _ _) $
                wk (step ρ) (∙ ⊢A′) ⊢A)
               (PE.subst₂ (_⊢_∷_ _)
                  (PE.sym $ lift-wk1 _ _)
                  (PE.sym $ lift-wk1 _ _) $
                wkTerm (step ρ) ⊢ΔA′ ⊢t)
               (PE.subst (_⊢_∷_ _ _) (wk1-wk≡lift-wk1 _ _) $
                var₀ ⊢A′)))
         ⊢B)
      (PE.subst (_ ⊢ _ ∷_)
         (wk-β-doubleSubst _ B _ _) $
       wkTerm ρ ⊢Δ ⊢u)
      (wkTerm ρ ⊢Δ ⊢t′) (wkRedTerm ρ ⊢Δ ⊢v)
    where
    ⊢A   = ⊢∙→⊢ (wf (⊢∙→⊢ (wf ⊢B)))
    ⊢A′  = wk ρ ⊢Δ ⊢A
    ⊢ΔA′ = ∙ ⊢A′
  wkRedTerm ρ ⊢Δ (K-subst {B = B} ⊢A ⊢t ⊢B ⊢u ⊢v ok) =
    PE.subst (_ ⊢ U.wk _ (K _ _ _ _ _ _) ⇒ _ ∷_)
      (PE.sym $ wk-β B) $
    K-subst ⊢A′ ⊢t′
      (wk (lift ρ) (∙ Idⱼ ⊢A′ ⊢t′ ⊢t′) ⊢B)
      (PE.subst (_ ⊢ _ ∷_) (wk-β B) $
       wkTerm ρ ⊢Δ ⊢u)
      (wkRedTerm ρ ⊢Δ ⊢v) ok
    where
    ⊢A′ = wk ρ ⊢Δ ⊢A
    ⊢t′ = wkTerm ρ ⊢Δ ⊢t
  wkRedTerm ρ ⊢Δ ([]-cong-subst A t u v ok) =
    []-cong-subst (wk ρ ⊢Δ A) (wkTerm ρ ⊢Δ t)
      (wkTerm ρ ⊢Δ u) (wkRedTerm ρ ⊢Δ v) ok
  wkRedTerm ρ ⊢Δ (J-β {B} ⊢t ⊢t′ t≡t′ ⊢B B≡B ⊢u) =
    PE.subst (_ ⊢ U.wk _ (J _ _ _ _ _ _ _ rfl) ⇒ _ ∷_)
      (PE.sym $ wk-β-doubleSubst _ B _ _) $
    J-β (wkTerm ρ ⊢Δ ⊢t) (wkTerm ρ ⊢Δ ⊢t′) (wkEqTerm ρ ⊢Δ t≡t′)
      (PE.subst₂ (λ A t → _ ∙ U.wk _ _ ∙ Id A t _ ⊢ _)
         (PE.sym $ wk1-wk≡lift-wk1 _ _)
         (PE.sym $ wk1-wk≡lift-wk1 _ _) $
       wk (lift (lift ρ))
         (∙ (Idⱼ
               (PE.subst (_⊢_ _) (PE.sym $ lift-wk1 _ _) $
                wk (step ρ) ⊢ΔA′ ⊢A)
               (PE.subst₂ (_⊢_∷_ _)
                  (PE.sym $ lift-wk1 _ _)
                  (PE.sym $ lift-wk1 _ _) $
                wkTerm (step ρ) ⊢ΔA′ ⊢t)
               (PE.subst (_⊢_∷_ _ _) (wk1-wk≡lift-wk1 _ _) $
                var₀ ⊢A′)))
         ⊢B)
      (PE.subst₂ (_ ⊢_≡_)
         (wk-β-doubleSubst _ B _ _)
         (wk-β-doubleSubst _ B _ _)
         (wkEq ρ ⊢Δ B≡B))
      (PE.subst (_ ⊢ _ ∷_) (wk-β-doubleSubst _ B _ _) $
       wkTerm ρ ⊢Δ ⊢u)
    where
    ⊢A   = ⊢∙→⊢ (wf (⊢∙→⊢ (wf ⊢B)))
    ⊢A′  = wk ρ ⊢Δ ⊢A
    ⊢ΔA′ = ∙ ⊢A′
  wkRedTerm ρ ⊢Δ (K-β {B = B} ⊢t ⊢B ⊢u ok) =
    PE.subst (_ ⊢ U.wk _ (K _ _ _ _ _ rfl) ⇒ _ ∷_)
      (PE.sym $ wk-β B) $
    K-β ⊢t′
      (wk (lift ρ) (∙ Idⱼ ⊢A′ ⊢t′ ⊢t′) ⊢B)
      (PE.subst (_ ⊢ _ ∷_) (wk-β B) $
       wkTerm ρ ⊢Δ ⊢u)
      ok
    where
    ⊢A′ = wk ρ ⊢Δ (inversion-Id-⊢ (⊢∙→⊢ (wf ⊢B)) .proj₁ .proj₁)
    ⊢t′ = wkTerm ρ ⊢Δ ⊢t
  wkRedTerm ρ ⊢Δ ([]-cong-β ⊢A ⊢t ⊢t′ t≡t′ ok) =
    []-cong-β (wk ρ ⊢Δ ⊢A) (wkTerm ρ ⊢Δ ⊢t) (wkTerm ρ ⊢Δ ⊢t′)
      (wkEqTerm ρ ⊢Δ t≡t′) ok

wkRed* : ρ ∷ Δ ⊇ Γ →
           let ρA = U.wk ρ A
               ρB = U.wk ρ B
           in ⊢ Δ → Γ ⊢ A ⇒* B → Δ ⊢ ρA ⇒* ρB
wkRed* ρ ⊢Δ (id A) = id (wk ρ ⊢Δ A)
wkRed* ρ ⊢Δ (A⇒A′ ⇨ A′⇒*B) = wkRed ρ ⊢Δ A⇒A′ ⇨ wkRed* ρ ⊢Δ A′⇒*B

wkRed*Term : ρ ∷ Δ ⊇ Γ →
           let ρA = U.wk ρ A
               ρt = U.wk ρ t
               ρu = U.wk ρ u
           in ⊢ Δ → Γ ⊢ t ⇒* u ∷ A → Δ ⊢ ρt ⇒* ρu ∷ ρA
wkRed*Term ρ ⊢Δ (id t) = id (wkTerm ρ ⊢Δ t)
wkRed*Term ρ ⊢Δ (t⇒t′ ⇨ t′⇒*u) = wkRedTerm ρ ⊢Δ t⇒t′ ⇨ wkRed*Term ρ ⊢Δ t′⇒*u

wkRed:*: : ρ ∷ Δ ⊇ Γ →
         let ρA = U.wk ρ A
             ρB = U.wk ρ B
         in ⊢ Δ → Γ ⊢ A :⇒*: B → Δ ⊢ ρA :⇒*: ρB
wkRed:*: ρ ⊢Δ [ ⊢A , ⊢B , D ] = [ wk ρ ⊢Δ ⊢A , wk ρ ⊢Δ ⊢B , wkRed* ρ ⊢Δ D ]

wkRed:*:Term : ρ ∷ Δ ⊇ Γ →
             let ρA = U.wk ρ A
                 ρt = U.wk ρ t
                 ρu = U.wk ρ u
             in ⊢ Δ → Γ ⊢ t :⇒*: u ∷ A → Δ ⊢ ρt :⇒*: ρu ∷ ρA
wkRed:*:Term ρ ⊢Δ [ ⊢t , ⊢u , d ] =
  [ wkTerm ρ ⊢Δ ⊢t , wkTerm ρ ⊢Δ ⊢u , wkRed*Term ρ ⊢Δ d ]

opaque

  -- Weakening for _⊢_↘_.

  wkRed↘ : ρ ∷ Δ ⊇ Γ → ⊢ Δ → Γ ⊢ A ↘ B → Δ ⊢ U.wk ρ A ↘ U.wk ρ B
  wkRed↘ ρ⊇ ⊢Δ = Σ.map (wkRed* ρ⊇ ⊢Δ) (wkWhnf _)

opaque

  -- Weakening for _⊢_↘_∷_.

  wkRed↘Term :
    ρ ∷ Δ ⊇ Γ → ⊢ Δ → Γ ⊢ t ↘ u ∷ A → Δ ⊢ U.wk ρ t ↘ U.wk ρ u ∷ U.wk ρ A
  wkRed↘Term ρ⊇ ⊢Δ = Σ.map (wkRed*Term ρ⊇ ⊢Δ) (wkWhnf _)
