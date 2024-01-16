------------------------------------------------------------------------
-- Prodrec for strong Σ-types and projections for weak Σ-types
------------------------------------------------------------------------

-- These definitions are part of an investigation of to what degree
-- weak Σ-types can emulate strong Σ-types, and vice versa. This
-- investigation was prompted by a question asked by an anonymous
-- reviewer. See also Definition.Typed.Consequences.DerivedRules.Sigma
-- and Graded.Derived.Sigma.

module Definition.Untyped.Sigma {a} (M : Set a) where

open import Definition.Untyped M

open import Tools.Fin
open import Tools.Nat using (Nat; 1+; 2+)

private variable
  n : Nat

-- A definition of prodrec for strong Σ-types.

prodrecˢ : M → Term n → Term (2+ n) → Term n
prodrecˢ p t u = u [ fst p t , snd p t ]

-- The projections are defined using some extra quantities r′ and q′.

module Fstʷ-sndʷ (r′ q′ : M) where

  -- The first projection.

  fstʷ : M → Term n → Term n → Term n
  fstʷ p A t = prodrec r′ p q′ (wk1 A) t (var x1)

  -- The second projection.

  sndʷ : M → M → Term n → Term (1+ n) → Term n → Term n
  sndʷ p q A B t =
    prodrec r′ p q (B [ fstʷ p (wk1 A) (var x0) ]↑) t (var x0)
