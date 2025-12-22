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
open import Definition.Typed.Decidable.Internal.Term 𝕄

open import Tools.Level
open import Tools.List
open import Tools.Maybe using (Maybe; just; nothing)
import Tools.PropositionalEquality as PE
open import Tools.String
open import Tools.Sum
open import Tools.Unit

private variable
  ℓ ℓ₁ ℓ₂ : Level
  A B     : Set _
  x y z   : A
  f       : A → B
  c       : Constants
  C       : Constraint _
  γ       : Contexts _

------------------------------------------------------------------------
-- The monad, along with some basic operations

-- A monad with failure (including error messages), checking of
-- constraints, and a reader component (contexts).

record Check (c : Constants) (A : Set ℓ) : Set (lsuc a ⊔ ℓ) where
  constructor wrap
  no-eta-equality
  field
    run : Contexts c → String ⊎ A

open Check public

-- Failure.

fail : String → Check c A
fail s .run _ = inj₁ s

-- The meta-context.

ask : Check c (Meta-con c)
ask .run γ = inj₂ (γ .metas)

-- | If the first computation fails, try the second one. In that case,
-- throw away the first computation's error message.

infixr 2 _catch_

_catch_ : Check c A → Check c A → Check c A
(m₁ catch m₂) .run γ with m₁ .run γ
… | inj₁ _     = m₂ .run γ
… | x@(inj₂ _) = x

-- Checking a constraint.

require : Constraint c → Check c ⊤
require C .run γ with member C (γ .constraints)
… | just _  = inj₂ tt
… | nothing = inj₁ "Failed to verify constraint."

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

-- Converts from Maybe to the monad.

infix 4 [_]with-message_

[_]with-message_ : Maybe A → String → Check c A
[ just x  ]with-message _ = return x
[ nothing ]with-message s = fail s

------------------------------------------------------------------------
-- The predicate OK

-- OK x y γ means that the computation x succeeded for γ and returned
-- y.

data OK {A : Set ℓ} (x : Check c A) (y : A) (γ : Contexts c) :
       Set (lsuc a ⊔ ℓ) where
  ok : x .run γ PE.≡ inj₂ y → OK x y γ

pattern not-ok = ok ()
pattern ok!    = ok PE.refl

opaque

  -- An inversion lemma for require.

  inv-require-∈ : OK (require C) tt γ → C ∈ γ .constraints
  inv-require-∈ {C} {γ} (ok eq) with member C (γ .constraints)
  inv-require-∈         not-ok | nothing
  inv-require-∈         ok!    | just C∈ = C∈

opaque

  -- An inversion lemma for _catch_.

  inv-catch : OK (x catch y) z γ → OK x z γ ⊎ OK y z γ
  inv-catch {x} {γ} (ok eq     ) with x .run γ in eq
  inv-catch         (ok PE.refl) | inj₂ _ = inj₁ (ok eq)
  inv-catch         (ok eq     ) | inj₁ _ = inj₂ (ok eq)

-- A type used to state inv->>=.

record Inv->>= {A : Set ℓ₁} {B : Set ℓ₂}
         (x : Check c A) (f : A → Check c B) (y : B) (γ : Contexts c) :
         Set (lsuc a ⊔ ℓ₁ ⊔ ℓ₂) where
  constructor inv
  field
    value : A
    ok₁   : OK x value γ
    ok₂   : OK (f value) y γ

opaque

  -- An inversion lemma for _>>=_.

  inv->>= : OK (x >>= f) y γ → Inv->>= x f y γ
  inv->>= {x} {γ} (ok _)       with x .run γ in eq₁
  inv->>=         not-ok       | inj₁ _
  inv->>= {f} {γ} _            | inj₂ y with f y .run γ in eq₂
  inv->>=         not-ok       | _      | inj₁ _
  inv->>=         (ok PE.refl) | inj₂ y | inj₂ _ =
    inv y (ok eq₁) (ok eq₂)

-- A type used to state inv-<$>.

data Inv-<$> {A : Set ℓ₁} {B : Set ℓ₂}
       (f : A → B) (x : Check c A) (y : B) (γ : Contexts c) :
       Set (lsuc a ⊔ ℓ₁ ⊔ ℓ₂) where
  inv : ∀ x′ → OK x x′ γ → f x′ PE.≡ y → Inv-<$> f x y γ

opaque

  -- An inversion lemma for _<$>_.

  inv-<$> : OK (f <$> x) y γ → Inv-<$> f x y γ
  inv-<$> eq
    with inv->>= eq
  … | inv _ eq ok! =
    inv _ eq PE.refl

-- A type used to state inv-⊛.

data Inv-⊛ {A : Set ℓ₁} {B : Set ℓ₂}
       (f : Check c (A → B)) (x : Check c A) (y : B) (γ : Contexts c) :
       Set (lsuc a ⊔ ℓ₁ ⊔ ℓ₂) where
  inv : ∀ f′ x′ → OK f f′ γ → OK x x′ γ → f′ x′ PE.≡ y → Inv-⊛ f x y γ

opaque

  -- An inversion lemma for _⊛_.

  inv-⊛ : OK (x ⊛ y) z γ → Inv-⊛ x y z γ
  inv-⊛ eq
    with inv->>= eq
  … | inv _ eq₁ eq
    with inv->>= eq
  … | inv _ eq₂ ok! =
    inv _ _ eq₁ eq₂ PE.refl
