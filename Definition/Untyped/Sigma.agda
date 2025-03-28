------------------------------------------------------------------------
-- Prodrec for strong Σ-types and projections for all Σ-types
------------------------------------------------------------------------

-- These definitions are part of an investigation of to what degree
-- weak Σ-types can emulate strong Σ-types, and vice versa. This
-- investigation was prompted by a question asked by an anonymous
-- reviewer. See also Definition.Typed.Properties.Admissible.Sigma,
-- Definition.Typed.Consequences.Admissible.Sigma, and
-- Graded.Derived.Sigma.

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
  s       : Strength
  p q r   : M

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
