------------------------------------------------------------------------
-- Definitions related to Σ-types
------------------------------------------------------------------------

open import Graded.Modality

module Definition.Untyped.Sigma
  {a} {M : Set a}
  (𝕄 : Modality M)
  where

open Modality 𝕄

open import Definition.Untyped M
open import Definition.Untyped.Properties M

open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+; 2+)
open import Tools.PropositionalEquality
open import Tools.Reasoning.PropositionalEquality

private variable
  n       : Nat
  A B t u : Term _
  σ       : Subst _ _
  ρ       : Wk _ _
  s       : Strength
  p q r   : M

------------------------------------------------------------------------
-- Some definitions related to the heterogeneous Σ type

opaque

  -- Heterogeneous pairs.

  prodʰ : Strength → M → (_ _ : Term n) → Term n
  prodʰ s p t u = prod s p (lift t) (lift u)

-- Heterogeneous strong pairs.

prodʰˢ : M → (_ _ : Term n) → Term n
prodʰˢ = prodʰ 𝕤

-- Heterogeneous weak pairs.

prodʰʷ : M → (_ _ : Term n) → Term n
prodʰʷ = prodʰ 𝕨

opaque

  -- A heterogeneous first projection.

  fstʰ : M → Term n → Term n
  fstʰ p t = lower (fst p t)

opaque

  -- A heterogeneous second projection.

  sndʰ : M → Term n → Term n
  sndʰ p t = lower (snd p t)

------------------------------------------------------------------------
-- Some substitution lemmas

opaque
  unfolding prodʰ

  -- A substitution lemma for prodʰ.

  prodʰ-[] : prodʰ s p t u [ σ ] ≡ prodʰ s p (t [ σ ]) (u [ σ ])
  prodʰ-[] = refl

opaque
  unfolding fstʰ

  -- A substitution lemma for fstʰ.

  fstʰ-[] : fstʰ p t [ σ ] ≡ fstʰ p (t [ σ ])
  fstʰ-[] = refl

opaque
  unfolding sndʰ

  -- A substitution lemma for sndʰ.

  sndʰ-[] : sndʰ p t [ σ ] ≡ sndʰ p (t [ σ ])
  sndʰ-[] = refl

------------------------------------------------------------------------
-- Some weakening lemmas

opaque

  -- A weakening lemma for prodʰ.

  wk-prodʰ : wk ρ (prodʰ s p t u) ≡ prodʰ s p (wk ρ t) (wk ρ u)
  wk-prodʰ {ρ} {s} {p} {t} {u} =
    wk ρ (prodʰ s p t u)                           ≡⟨ wk≡subst _ _ ⟩
    prodʰ s p t u [ toSubst ρ ]                    ≡⟨ prodʰ-[] ⟩
    prodʰ s p (t [ toSubst ρ ]) (u [ toSubst ρ ])  ≡˘⟨ cong₂ (prodʰ _ _) (wk≡subst _ _) (wk≡subst _ _) ⟩
    prodʰ s p (wk ρ t) (wk ρ u)                    ∎

opaque

  -- A weakening lemma for fstʰ.

  wk-fstʰ : wk ρ (fstʰ p t) ≡ fstʰ p (wk ρ t)
  wk-fstʰ {ρ} {p} {t} =
    wk ρ (fstʰ p t)           ≡⟨ wk≡subst _ _ ⟩
    fstʰ p t [ toSubst ρ ]    ≡⟨ fstʰ-[] ⟩
    fstʰ p (t [ toSubst ρ ])  ≡˘⟨ cong (fstʰ _) $ wk≡subst _ _ ⟩
    fstʰ p (wk ρ t)           ∎

opaque

  -- A weakening lemma for sndʰ.

  wk-sndʰ : wk ρ (sndʰ p t) ≡ sndʰ p (wk ρ t)
  wk-sndʰ {ρ} {p} {t} =
    wk ρ (sndʰ p t)           ≡⟨ wk≡subst _ _ ⟩
    sndʰ p t [ toSubst ρ ]    ≡⟨ sndʰ-[] ⟩
    sndʰ p (t [ toSubst ρ ])  ≡˘⟨ cong (sndʰ _) $ wk≡subst _ _ ⟩
    sndʰ p (wk ρ t)           ∎

------------------------------------------------------------------------
-- Prodrec for strong Σ-types and projections for all Σ-types

-- These definitions are part of an investigation of to what degree
-- weak Σ-types can emulate strong Σ-types, and vice versa. This
-- investigation was prompted by a question asked by an anonymous
-- reviewer. See also Definition.Typed.Properties.Admissible.Sigma,
-- Definition.Typed.Consequences.Admissible.Sigma, and
-- Graded.Derived.Sigma.

-- A definition of prodrec for strong Σ-types.

prodrecˢ : M → Term n → Term (2+ n) → Term n
prodrecˢ p t u = u [ fst p t , snd p t ]₁₀

opaque

  -- A variant of prodrec for all kinds of Σ-types.

  prodrec⟨_⟩ :
    Strength → M → M → M → Term (1+ n) → Term n → Term (2+ n) → Term n
  prodrec⟨ 𝕨 ⟩ = prodrec
  prodrec⟨ 𝕤 ⟩ = λ _ p _ _ t u → prodrecˢ p t u

opaque
  unfolding prodrec⟨_⟩

  -- A substitution lemma for prodrec⟨_⟩.

  prodrec⟨⟩-[] :
    prodrec⟨ s ⟩ r p q A t u [ σ ] ≡
    prodrec⟨ s ⟩ r p q (A [ liftSubst σ ]) (t [ σ ])
      (u [ liftSubstn σ 2 ])
  prodrec⟨⟩-[] {s = 𝕨} =
    refl
  prodrec⟨⟩-[] {s = 𝕤} {p} {t} {u} {σ} =
    u [ fst p t , snd p t ]₁₀ [ σ ]                               ≡⟨ [,]-[]-commute u ⟩
    u [ liftSubstn σ 2 ] [ fst p (t [ σ ]) , snd p (t [ σ ]) ]₁₀  ∎

-- The projections are defined using some extra quantities r′ and q′.

module Fstʷ-sndʷ (r′ q′ : M) where

  -- The first projection.

  fstʷ : M → Term n → Term n → Term n
  fstʷ p A t = prodrec r′ p q′ (wk1 A) t (var x1)

  -- The second projection.

  sndʷ : M → M → Term n → Term (1+ n) → Term n → Term n
  sndʷ p q A B t =
    prodrec r′ p q (B [ fstʷ p (wk1 A) (var x0) ]↑) t (var x0)

  opaque

    -- A substitution lemma for fstʷ.

    fstʷ-[] : ∀ A t → fstʷ p A t [ σ ] ≡ fstʷ p (A [ σ ]) (t [ σ ])
    fstʷ-[] {p} {σ} A t =
      fstʷ p A t [ σ ]                                            ≡⟨⟩
      prodrec r′ p q′ (wk1 A [ liftSubst σ ]) (t [ σ ]) (var x1)  ≡⟨ cong (λ A → prodrec _ _ _ A _ _) (wk1-liftSubst A) ⟩
      prodrec r′ p q′ (wk1 (A [ σ ])) (t [ σ ]) (var x1)          ≡⟨⟩
      fstʷ p (A [ σ ]) (t [ σ ])                                  ∎

  opaque

    -- A substitution lemma for sndʷ.

    sndʷ-[] :
      ∀ B t →
      sndʷ p q A B t [ σ ] ≡
      sndʷ p q (A [ σ ]) (B [ liftSubst σ ]) (t [ σ ])
    sndʷ-[] {p} {q} {A} {σ} B t =
      sndʷ p q A B t [ σ ]                                                ≡⟨⟩

      prodrec r′ p q
        (B [ fstʷ p (wk1 A) (var x0) ]↑ [ liftSubst σ ])
        (t [ σ ]) (var x0)                                                ≡⟨ cong (λ B → prodrec _ _ _ B _ _) $
                                                                             singleSubstLift↑ _ B _ ⟩
      prodrec r′ p q
        (B [ liftSubst σ ] [ fstʷ p (wk1 A) (var x0) [ liftSubst σ ] ]↑)
        (t [ σ ]) (var x0)                                                ≡⟨ cong (λ B → prodrec _ _ _ B _ _) $
                                                                             cong (λ t → B [ liftSubst σ ] [ t ]↑) $
                                                                             fstʷ-[] (wk1 A) (var x0) ⟩
      prodrec r′ p q
        (B [ liftSubst σ ] [ fstʷ p (wk1 A [ liftSubst σ ]) (var x0) ]↑)
        (t [ σ ]) (var x0)                                                ≡⟨ cong (λ B → prodrec _ _ _ B _ _) $
                                                                             cong (λ A → B [ _ ] [ fstʷ _ A _ ]↑) $
                                                                             wk1-liftSubst A ⟩
      prodrec r′ p q
        (B [ liftSubst σ ] [ fstʷ p (wk1 (A [ σ ])) (var x0) ]↑)
        (t [ σ ]) (var x0)                                                ≡⟨⟩

      sndʷ p q (A [ σ ]) (B [ liftSubst σ ]) (t [ σ ])                    ∎

-- The quantities "p" and "q" are instantiated based on an analysis
-- performed in Graded.Derived.Sigma.

open Fstʷ-sndʷ (𝟘 ∧ 𝟙) 𝟘 public

opaque

  -- A variant of fst for all kinds of Σ-types.

  fst⟨_⟩ : Strength → M → Term n → Term n → Term n
  fst⟨ 𝕤 ⟩ p _ t = fst p t
  fst⟨ 𝕨 ⟩ p A t = fstʷ p A t

opaque

  -- A variant of snd for all kinds of Σ-types.

  snd⟨_⟩ : Strength → M → M → Term n → Term (1+ n) → Term n → Term n
  snd⟨ 𝕤 ⟩ p _ _ _ t = snd p t
  snd⟨ 𝕨 ⟩ p q A B t = sndʷ p q A B t

opaque
  unfolding fst⟨_⟩

  -- A substitution lemma for fst⟨_⟩.

  fst⟨⟩-[] : fst⟨ s ⟩ p A t [ σ ] ≡ fst⟨ s ⟩ p (A [ σ ]) (t [ σ ])
  fst⟨⟩-[] {s = 𝕤}         = refl
  fst⟨⟩-[] {s = 𝕨} {A} {t} = fstʷ-[] A t

opaque
  unfolding snd⟨_⟩

  -- A substitution lemma for snd⟨_⟩.

  snd⟨⟩-[] :
    snd⟨ s ⟩ p q A B t [ σ ] ≡
    snd⟨ s ⟩ p q (A [ σ ]) (B [ liftSubst σ ]) (t [ σ ])
  snd⟨⟩-[] {s = 𝕤}         = refl
  snd⟨⟩-[] {s = 𝕨} {B} {t} = sndʷ-[] B t

opaque

  -- A witness for a propositional η-rule.

  Σʷ-η-prodʷ-fstʷ-sndʷ :
    M → M → Term n → Term (1+ n) → Term n → Term n
  Σʷ-η-prodʷ-fstʷ-sndʷ p q A B t =
    prodrec 𝟘 p 𝟙
      (Id (wk1 (Σʷ p , q ▷ A ▹ B))
         (prodʷ p (fstʷ p (wk1 A) (var x0))
            (sndʷ p q (wk1 A) (wk (lift (step id)) B) (var x0)))
         (var x0))
      t
      rfl

opaque

  -- A witness for a propositional η-rule.

  Σ⟨_⟩-η-prod-fst-snd :
    Strength → M → M → Term n → Term (1+ n) → Term n → Term n
  Σ⟨ 𝕤 ⟩-η-prod-fst-snd = λ _ _ _ _ _ → rfl
  Σ⟨ 𝕨 ⟩-η-prod-fst-snd = Σʷ-η-prodʷ-fstʷ-sndʷ
