------------------------------------------------------------------------
-- The type constructor Erased
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

open import Graded.Modality
open import Definition.Untyped.NotParametrised

module Graded.Derived.Erased.Untyped
  {a} {M : Set a}
  (𝕄 : Modality M)
  (s : Strength)
  where

open Modality 𝕄

open import Definition.Untyped M as U
open import Definition.Untyped.Identity 𝕄
open import Definition.Untyped.Properties M

import Graded.Derived.Erased.Eta.Untyped 𝕄 as Eta
import Graded.Derived.Erased.NoEta.Untyped 𝕄 as NoEta

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality as PE hiding (subst; cong)
open import Tools.Reasoning.PropositionalEquality

private variable
  n           : Nat
  A B t u v w : Term _
  σ           : Subst _ _

-- The type constructor Erased.

Erased : Term n → Term n
Erased A = Σ⟨ s ⟩ 𝟘 , 𝟘 ▷ A ▹ Unit s

-- The constructor [_].

[_] : Term n → Term n
[ t ] = prod s 𝟘 t (star s)

opaque

  -- The "projection" erased.

  erased : Term n → Term n → Term n
  erased A t = case s of λ where
    𝕤 → Eta.erased t
    𝕨 → NoEta.erased A t

opaque
  unfolding erased

  -- A substitution lemma for erased.

  erased-[] : erased A t U.[ σ ] ≡ erased (A U.[ σ ]) (t U.[ σ ])
  erased-[] {A} {t} = case singleton s of λ where
    (𝕤 , refl) → refl
    (𝕨 , refl) → NoEta.erased-[] A t

opaque

  -- Substitutivity.
  --
  -- This variant of subst is an alternative to subst 𝟘.

  substᵉ :
    Term n → Term (1+ n) → Term n → Term n → Term n → Term n → Term n
  substᵉ A B t u v w =
    subst 𝟘 (Erased A) (B [ erased (wk1 A) (var x0) ]↑) [ t ] [ u ]
      ([]-cong s A t u v) w

opaque
  unfolding substᵉ

  -- A substitution lemma for substᵉ.

  substᵉ-[] :
    substᵉ A B t u v w U.[ σ ] ≡
    substᵉ (A U.[ σ ]) (B U.[ liftSubst σ ]) (t U.[ σ ]) (u U.[ σ ])
      (v U.[ σ ]) (w U.[ σ ])
  substᵉ-[] {A} {B} {t} {u} {v} {w} {σ} =
    subst 𝟘 (Erased A) (B [ erased (wk1 A) (var x0) ]↑) [ t ] [ u ]
      ([]-cong s A t u v) w U.[ σ ]                                       ≡⟨ subst-[] ⟩

    subst 𝟘 (Erased A U.[ σ ])
      (B [ erased (wk1 A) (var x0) ]↑ U.[ liftSubst σ ]) ([ t ] U.[ σ ])
      ([ u ] U.[ σ ]) ([]-cong s A t u v U.[ σ ]) (w U.[ σ ])             ≡⟨ cong₅ (subst _ _) lemma refl refl refl refl ⟩

    subst 𝟘 (Erased (A U.[ σ ]))
      (B U.[ liftSubst σ ] [ erased (wk1 (A U.[ σ ])) (var x0) ]↑)
      [ t U.[ σ ] ] [ u U.[ σ ] ]
      ([]-cong s (A U.[ σ ]) (t U.[ σ ]) (u U.[ σ ]) (v U.[ σ ]))
      (w U.[ σ ])                                                         ∎
    where
    lemma :
      B [ erased (wk1 A) (var x0) ]↑ U.[ liftSubst σ ] ≡
      B U.[ liftSubst σ ] [ erased (wk1 (A U.[ σ ])) (var x0) ]↑
    lemma =
      B [ erased (wk1 A) (var x0) ]↑ U.[ liftSubst σ ]                    ≡⟨ singleSubstLift↑ _ B _ ⟩
      B U.[ liftSubst σ ] [ erased (wk1 A) (var x0) U.[ liftSubst σ ] ]↑  ≡⟨ PE.cong (B U.[ _ ] [_]↑) erased-[] ⟩
      B U.[ liftSubst σ ] [ erased (wk1 A U.[ liftSubst σ ]) (var x0) ]↑  ≡⟨ PE.cong (λ A → B U.[ _ ] [ erased A _ ]↑) $ wk1-liftSubst A ⟩
      B U.[ liftSubst σ ] [ erased (wk1 (A U.[ σ ])) (var x0) ]↑          ∎
