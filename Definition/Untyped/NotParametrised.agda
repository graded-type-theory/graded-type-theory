------------------------------------------------------------------------
-- Some definitions that are re-exported from Definition.Untyped but
-- do not depend on that module's module parameter
------------------------------------------------------------------------

module Definition.Untyped.NotParametrised where

open import Tools.Fin
open import Tools.Level
open import Tools.List
open import Tools.Nat

private variable
  a : Level

------------------------------------------------------------------------
-- Definitions related to terms

-- Typing contexts (length indexed snoc-lists, isomorphic to lists).
-- Terms added to the context are well scoped in the sense that it cannot
-- contain more unbound variables than can be looked up in the context.

infixl 30 _∙_

data Con (A : Nat → Set a) : Nat → Set a where
  ε   :                             Con A 0        -- Empty context.
  _∙_ : {n : Nat} → Con A n → A n → Con A (1+ n)   -- Context extension.

-- Representation of sub terms using a list of binding levels

infixr 5 _∷_

data GenTs (A : Nat → Set a) : Nat → List Nat → Set a where
  []  : {n : Nat} → GenTs A n []
  _∷_ : {n b : Nat} {bs : List Nat} (t : A (b + n)) (ts : GenTs A n bs) → GenTs A n (b ∷ bs)

-- Sigma types have two modes, allowing either projections or prodrec
data SigmaMode : Set where
  Σₚ Σᵣ : SigmaMode

-- Π- or Σ-types.

data BinderMode : Set where
  BMΠ : BinderMode
  BMΣ : (s : SigmaMode) → BinderMode

------------------------------------------------------------------------
-- Weakening

-- In the following we define untyped weakenings η : Wk.
-- The typed form could be written η : Γ ≤ Δ with the intention
-- that η transport a term t living in context Δ to a context Γ
-- that can bind additional variables (which cannot appear in t).
-- Thus, if Δ ⊢ t : A and η : Γ ≤ Δ then Γ ⊢ wk η t : wk η A.
--
-- Even though Γ is "larger" than Δ we write Γ ≤ Δ to be conformant
-- with subtyping A ≤ B.  With subtyping, relation Γ ≤ Δ could be defined as
-- ``for all x ∈ dom(Δ) have Γ(x) ≤ Δ(x)'' (in the sense of subtyping)
-- and this would be the natural extension of weakenings.

data Wk : Nat → Nat → Set where
  id    : {n : Nat}   → Wk n n                    -- η : Γ ≤ Γ.
  step  : {n m : Nat} → Wk m n → Wk (1+ m) n      -- If η : Γ ≤ Δ then step η : Γ∙A ≤ Δ.
  lift  : {n m : Nat} → Wk m n → Wk (1+ m) (1+ n) -- If η : Γ ≤ Δ then lift η : Γ∙A ≤ Δ∙A.

-- Composition of weakening.
-- If η : Γ ≤ Δ and η′ : Δ ≤ Φ then η • η′ : Γ ≤ Φ.

infixl 30 _•_

_•_                :  {l m n : Nat} → Wk l m → Wk m n → Wk l n
id      • η′       =  η′
step η  • η′       =  step  (η • η′)
lift η  • id       =  lift  η
lift η  • step η′  =  step  (η • η′)
lift η  • lift η′  =  lift  (η • η′)

liftn : {k m : Nat} → Wk k m → (n : Nat) → Wk (n + k) (n + m)
liftn ρ 0 = ρ
liftn ρ (1+ n) = lift (liftn ρ n)

-- Weakening of variables.
-- If η : Γ ≤ Δ and x ∈ dom(Δ) then wkVar η x ∈ dom(Γ).

wkVar : {m n : Nat} (ρ : Wk m n) (x : Fin n) → Fin m
wkVar id x            = x
wkVar (step ρ) x      = (wkVar ρ x) +1
wkVar (lift ρ) x0     = x0
wkVar (lift ρ) (x +1) = (wkVar ρ x) +1
