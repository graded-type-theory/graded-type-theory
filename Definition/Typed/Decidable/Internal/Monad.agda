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
  ℓ ℓ₁ ℓ₂   : L.Level
  A B       : Set _
  x y z     : A
  f         : A → B
  xs ys     : List _
  b         : Bool
  m n n₁ n₂ : Nat
  c         : Constants
  γ         : Contexts _
  C         : Constraint _

------------------------------------------------------------------------
-- The monad, along with some basic operations

-- Stack trace entries.

data Call (c : Constants) : Set a where
  [red] [red-ty] [check-type] [check-level] [infer] [normalise-level] :
    Cons c m n → Term c n → Call c
  [red-tm] [check] [equal-ty] [equal-ne-inf] :
    Cons c m n → (_ _ : Term c n) → Call c
  [equal-tm] :
    Cons c m n → (_ _ _ : Term c n) → Call c
  [check-sub] :
    DCon c m → Con c n₂ → Subst c n₂ n₁ → Con c n₁ → Call c

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

-- Runs the computation if the boolean is "false".

unless : Bool → Check c ⊤ → Check c ⊤
unless true  _ = return tt
unless false x = x

-- Short-circuiting and.

and : Check c Bool → Check c Bool → Check c Bool
and x y = do
  b ← x
  if b then y else return false

-- Short-circuiting or.

or : Check c Bool → Check c Bool → Check c Bool
or x y = do
  b ← x
  if b then return true else y

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

-- Checks if equality reflection is disallowed.

no-equality-reflection? : Check c Bool
no-equality-reflection? =
  (require no-equality-reflection >> return true)
    catch
  return false

-- Does one thing if equality reflection is definitely disallowed, and
-- another thing if equality reflection is possibly allowed.

if-no-equality-reflection : Check c A → Check c A → Check c A
if-no-equality-reflection x y = do
  disallowed ← no-equality-reflection?
  if disallowed then x else y

-- Converts from Maybe to the monad.

infix 4 [_]with-message_

[_]with-message_ : Maybe A → String → Check c A
[ just x  ]with-message _ = return x
[ nothing ]with-message s = fail s

------------------------------------------------------------------------
-- Fuel

-- The type of "fuel" used to ensure termination of some definitions.

Fuel : Set
Fuel = Nat

-- A computation that fails with the error message "No fuel left.". No
-- stack trace is returned.

no-fuel : Check c A
no-fuel .run _ = inj₁ ("No fuel left." , [])

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

  -- The computation register cl x succeeds if x succeeds (with a
  -- certain call stack).

  OK-register :
    OK x y γ (cl ∷ st) →
    OK (register cl x) y γ st
  OK-register (ok eq) = ok eq

opaque

  -- An inversion lemma for register.

  inv-register :
    OK (register cl chk) x γ st →
    OK chk x γ (cl ∷ st)
  inv-register (ok eq) = ok eq

opaque

  -- The computation x catch y succeeds if x succeeds or y succeeds.

  OK-catch :
    (∃ λ z → OK x z γ st) ⊎ (∃ λ z → OK y z γ st) →
    ∃ λ z → OK (x catch y) z γ st
  OK-catch eq = let _ , eq = lemma eq in _ , ok eq
    where
    lemma :
      (∃ λ z → OK x z γ st) ⊎ (∃ λ z → OK y z γ st) →
      ∃ λ z → (x catch y) .run (γ # st) PE.≡ inj₂ z
    lemma {x} {γ} {st} (inj₁ (_ , ok _))   with x .run (γ # st)
    lemma              (inj₁ (_ , not-ok)) | inj₁ _
    lemma              _                   | inj₂ _ = _ , PE.refl
    lemma {x} {γ} {st} (inj₂ _)            with x .run (γ # st)
    lemma              _                   | inj₂ _ = _ , PE.refl
    lemma {γ} {st} {y} (inj₂ (_ , ok _))   | inj₁ _ with y .run (γ # st)
    lemma              (inj₂ (_ , not-ok)) | inj₁ _ | inj₁ _
    lemma              _                   | inj₁ _ | inj₂ _ =
      _ , PE.refl

opaque

  -- An inversion lemma for _catch_.

  inv-catch : OK (x catch y) z γ st → OK x z γ st ⊎ OK y z γ st
  inv-catch {x} {γ} {st} (ok eq) with x .run (γ # st) in eq
  inv-catch         (ok PE.refl) | inj₂ _ = inj₁ (ok eq)
  inv-catch         (ok eq     ) | inj₁ _ = inj₂ (ok eq)

opaque

  -- The computation x >>= f succeeds if x succeeds with the value y
  -- and f y succeeds (with the same contexts and call stack).

  OK->>= :
    OK x y γ st → OK (f y) z γ st → OK (x >>= f) z γ st
  OK->>= eq₁ eq₂ = ok (lemma eq₁ eq₂)
    where
    lemma :
      OK x y γ st → OK (f y) z γ st →
      (x >>= f) .run (γ # st) PE.≡ inj₂ z
    lemma {x} {γ} {st} (ok _) _      with x .run (γ # st)
    lemma              not-ok _      | inj₁ _
    lemma {γ} {st} {f} ok!    (ok _) | inj₂ y with f y .run (γ # st)
    lemma              ok!    not-ok | inj₂ _ | inj₁ _
    lemma              ok!    ok!    | inj₂ _ | inj₂ _ = PE.refl

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

  -- An inversion lemma for unless.

  inv-unless : b PE.≡ false → OK (unless b x) tt γ st → OK x tt γ st
  inv-unless PE.refl = idᶠ

opaque

  -- An inversion lemma for and.

  inv-and : OK (and x y) true γ st → OK x true γ st × OK y true γ st
  inv-and eq
    with inv->>= eq
  … | inv false _   not-ok
  … | inv true  eq₁ eq₂    =
    eq₁ , eq₂

opaque

  -- An inversion lemma for or.

  inv-or : OK (or x y) true γ st → OK x true γ st ⊎ OK y true γ st
  inv-or eq with inv->>= eq
  … | inv true  eq ok! = inj₁ eq
  … | inv false _  eq  = inj₂ eq

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

opaque

  -- The computation no-equality-reflection? always succeeds.

  OK-no-equality-reflection? :
    ∃ λ b → OK no-equality-reflection? b γ st
  OK-no-equality-reflection? = OK-catch (inj₂ (_ , ok!))

opaque

  -- An inversion lemma for no-equality-reflection?.

  inv-no-equality-reflection?-∈ :
    OK no-equality-reflection? true γ st →
    no-equality-reflection ∈ γ .constraints
  inv-no-equality-reflection?-∈ eq with inv-catch eq
  … | inj₂ not-ok
  … | inj₁ eq     =
    let inv _ eq _ = inv->>= eq in
    inv-require-∈ eq

opaque

  -- The computation if-no-equality-reflection x y succeeds with the
  -- value z if x and y both succeed with the value z (and the same
  -- contexts and call stack).

  OK-if-no-equality-reflection :
    OK x z γ st → OK y z γ st →
    OK (if-no-equality-reflection x y) z γ st
  OK-if-no-equality-reflection {γ} {st} eq₁ eq₂
    with OK-no-equality-reflection? {γ = γ} {st = st}
  … | true  , eq = OK->>= eq eq₁
  … | false , eq = OK->>= eq eq₂

opaque

  -- An inversion lemma for if-no-equality-reflection.

  inv-if-no-equality-reflection-∈ :
    OK (if-no-equality-reflection x y) z γ st →
    no-equality-reflection ∈ γ .constraints × OK x z γ st ⊎
    OK y z γ st
  inv-if-no-equality-reflection-∈ eq with inv->>= eq
  … | inv true  eq₁ eq₂ = inj₁ (inv-no-equality-reflection?-∈ eq₁ , eq₂)
  … | inv false _   eq₂ = inj₂ eq₂
