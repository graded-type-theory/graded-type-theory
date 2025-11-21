------------------------------------------------------------------------
-- A monad used by Definition.Typed.Decidable.Internal
------------------------------------------------------------------------

-- This "monad" may or may not satisfy the monad laws, no such proof
-- is included here.

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Decidable.Internal.Monad
  {a} {M : Set a}
  {𝕄 : Modality M}
  (TR : Type-restrictions 𝕄)
  where

open import Definition.Typed.Decidable.Internal.Constraint TR
open import Definition.Typed.Decidable.Internal.Term TR

open import Tools.Bool
open import Tools.Function
open import Tools.Level as L
open import Tools.List
open import Tools.Maybe using (Maybe; just; nothing)
open import Tools.Nat using (Nat)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.String
open import Tools.Sum
open import Tools.Unit

open Any using (Any)

private variable
  ℓ ℓ₁ ℓ₂ : L.Level
  A B     : Set _
  x y z   : A
  f       : A → B
  xs ys   : List _
  b       : Bool
  m n     : Nat
  c       : Constants
  γ       : Contexts _
  C       : Constraint _

------------------------------------------------------------------------
-- The monad, along with some basic operations

-- Stack trace entries.

data Call (c : Constants) : Set a where
  [red-ty] [check-type] [check-level] [infer] [normalise-level] :
    Cons c m n → Term c n → Call c
  [red-tm] [check] [equal-ty] [equal-ne-inf] :
    Cons c m n → (_ _ : Term c n) → Call c
  [equal-tm] :
    Cons c m n → (_ _ _ : Term c n) → Call c

-- Stack traces.

Stack-trace : Constants → Set a
Stack-trace c = List (Call c)

private variable
  cl : Call _
  st : Stack-trace _

-- The monad's reader component.

record Monad-con (c : Constants) : Set a where
  constructor _#_
  no-eta-equality
  field
    contexts    : Contexts c
    stack-trace : Stack-trace c

open Monad-con public

-- A monad with failure (including error messages), checking of
-- constraints, stack traces, and a reader component (contexts).

record Check (c : Constants) (A : Set ℓ) : Set (lsuc a ⊔ ℓ) where
  constructor wrap
  no-eta-equality
  field
    run : Monad-con c → String × List (Call c) ⊎ A

open Check public

private variable
  chk : Check _ _

-- Failure.

fail : String → Check c A
fail s .run Μ = inj₁ (s , Μ .stack-trace)

-- Registering a call in the stack trace.

register : Call c → Check c A → Check c A
register c comp .run Μ =
  comp .run (record Μ { stack-trace = c ∷ Μ .stack-trace })

-- The contexts.

ask : Check c (Contexts c)
ask .run γ = inj₂ (γ .contexts)

-- | If the first computation fails, try the second one. In that case,
-- throw away the first computation's error message.

infixr 2 _catch_

_catch_ : Check c A → Check c A → Check c A
(m₁ catch m₂) .run γ with m₁ .run γ
… | inj₁ _     = m₂ .run γ
… | x@(inj₂ _) = x

-- The monad's return operation.

return : A → Check c A
return x .run _ = inj₂ x

-- The monad's bind operation.

infixl 1 _>>=_

_>>=_ : Check c A → (A → Check c B) → Check c B
(m >>= f) .run γ with m .run γ
… | inj₁ s         = inj₁ s
… | inj₂ x with f x .run γ
…   | inj₁ s = inj₁ s
…   | inj₂ y = inj₂ y

-- A variant of _>>=_.

infixl 1 _>>_

_>>_ : Check c A → Check c B → Check c B
x >> y = x >>= λ _ → y

-- A map function.

infixl 3 _<$>_

_<$>_ : (A → B) → Check c A → Check c B
f <$> x = do
  x ← x
  return (f x)

-- Applicative functor application.

infixl 3 _⊛_

_⊛_ : Check c (A → B) → Check c A → Check c B
f ⊛ x = do
  f ← f
  x ← x
  return (f x)

-- Runs the computation if the boolean is "true".

when : Bool → Check c ⊤ → Check c ⊤
when true  x = x
when false _ = return tt

-- The computation succeeds if the predicate holds for all arguments
-- in the list.

all : (A → Check c ⊤) → List A → Check c ⊤
all _ []       = return tt
all f (x ∷ xs) = f x >> all f xs

-- The computation succeeds if the predicate holds for some argument
-- in the list.

any : (A → Check c ⊤) → List A → Check c ⊤
any _ []       = fail "Empty list."
any f (x ∷ xs) = f x catch any f xs

-- Checking a constraint.

require : Constraint c → Check c ⊤
require C = do
  Μ ← ask
  case member? _≟ᶜ_ C (Μ .constraints) of λ where
    (just _) → return tt
    nothing  → fail "Failed to verify constraint."

-- Converts from Maybe to the monad.

infix 4 [_]with-message_

[_]with-message_ : Maybe A → String → Check c A
[ just x  ]with-message _ = return x
[ nothing ]with-message s = fail s

------------------------------------------------------------------------
-- The predicate OK

-- OK x y st γ means that the computation x succeeded for st and γ and
-- returned y.

data OK {A : Set ℓ} (x : Check c A) (y : A) (γ : Contexts c)
       (st : Stack-trace c) : Set (lsuc a ⊔ ℓ) where
  ok : x .run (γ # st) PE.≡ inj₂ y → OK x y γ st

pattern not-ok = ok ()
pattern ok!    = ok PE.refl

opaque

  -- An inversion lemma for register.

  inv-register :
    OK (register cl chk) x γ st →
    OK chk x γ (cl ∷ st)
  inv-register (ok eq) = ok eq

opaque

  -- An inversion lemma for _catch_.

  inv-catch : OK (x catch y) z γ st → OK x z γ st ⊎ OK y z γ st
  inv-catch {x} {γ} {st} (ok eq) with x .run (γ # st) in eq
  inv-catch         (ok PE.refl) | inj₂ _ = inj₁ (ok eq)
  inv-catch         (ok eq     ) | inj₁ _ = inj₂ (ok eq)

-- A type used to state inv->>=.

record Inv->>= {A : Set ℓ₁} {B : Set ℓ₂}
         (x : Check c A) (f : A → Check c B) (y : B) (γ : Contexts c)
         (st : Stack-trace c) : Set (lsuc a ⊔ ℓ₁ ⊔ ℓ₂) where
  constructor inv
  field
    value : A
    ok₁   : OK x value γ st
    ok₂   : OK (f value) y γ st

opaque

  -- An inversion lemma for _>>=_.

  inv->>= : OK (x >>= f) y γ st → Inv->>= x f y γ st
  inv->>= {x} {γ} {st} (ok _) with x .run (γ # st) in eq₁
  inv->>=              not-ok | inj₁ _
  inv->>= {f} {γ} {st} _      | inj₂ y
   with f y .run (γ # st) in eq₂
  inv->>= not-ok       | _      | inj₁ _
  inv->>= (ok PE.refl) | inj₂ y | inj₂ _ =
    inv y (ok eq₁) (ok eq₂)

-- A type used to state inv-<$>.

data Inv-<$> {A : Set ℓ₁} {B : Set ℓ₂}
       (f : A → B) (x : Check c A) (y : B) (γ : Contexts c)
       (st : Stack-trace c) : Set (lsuc a ⊔ ℓ₁ ⊔ ℓ₂) where
  inv : ∀ x′ → OK x x′ γ st → f x′ PE.≡ y → Inv-<$> f x y γ st

opaque

  -- An inversion lemma for _<$>_.

  inv-<$> : OK (f <$> x) y γ st → Inv-<$> f x y γ st
  inv-<$> eq
    with inv->>= eq
  … | inv _ eq ok! =
    inv _ eq PE.refl

-- A type used to state inv-⊛.

data Inv-⊛ {A : Set ℓ₁} {B : Set ℓ₂}
       (f : Check c (A → B)) (x : Check c A) (y : B) (γ : Contexts c)
       (st : Stack-trace c) : Set (lsuc a ⊔ ℓ₁ ⊔ ℓ₂) where
  inv : ∀ f′ x′ → OK f f′ γ st → OK x x′ γ st → f′ x′ PE.≡ y →
        Inv-⊛ f x y γ st

opaque

  -- An inversion lemma for _⊛_.

  inv-⊛ : OK (x ⊛ y) z γ st → Inv-⊛ x y z γ st
  inv-⊛ eq
    with inv->>= eq
  … | inv _ eq₁ eq
    with inv->>= eq
  … | inv _ eq₂ ok! =
    inv _ _ eq₁ eq₂ PE.refl

opaque

  -- An inversion lemma for when.

  inv-when : b PE.≡ true → OK (when b x) tt γ st → OK x tt γ st
  inv-when PE.refl = idᶠ

opaque

  -- An inversion lemma for all.

  inv-all : OK (all f xs) tt γ st → All (λ x → OK (f x) tt γ st) xs
  inv-all {xs = []}    ok! = []
  inv-all {xs = _ ∷ _} eq
    with inv->>= eq
  … | inv _ eq₁ eq =
    eq₁ ∷ inv-all eq

opaque

  -- An inversion lemma for any.

  inv-any : OK (any f xs) tt γ st → Any (λ x → OK (f x) tt γ st) xs
  inv-any {xs = []}    not-ok
  inv-any {xs = _ ∷ _} eq
    with inv-catch eq
  … | inj₁ eq =
    here eq
  … | inj₂ eq =
    there (inv-any eq)

opaque

  -- An inversion lemma for require.

  inv-require-∈ : OK (require C) tt γ st → C ∈ γ .constraints
  inv-require-∈ {C} {γ} (ok eq) with member? _≟ᶜ_ C (γ .constraints)
  inv-require-∈ not-ok | nothing
  inv-require-∈ ok!    | just C∈ = C∈
