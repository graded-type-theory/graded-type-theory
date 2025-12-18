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

open import Definition.Typed.Decidable.Internal.Constraints TR
open import Definition.Typed.Decidable.Internal.Term TR

open import Tools.Function
open import Tools.Level
open import Tools.Maybe using (Maybe; just; nothing)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.String
open import Tools.Sum
open import Tools.Unit

private variable
  ℓ ℓ₁ ℓ₂ : Level
  A B     : Set _
  x y z   : A
  f       : A → B
  c       : Constants
  γ       : Contexts _
  Cs      : Constraints _

------------------------------------------------------------------------
-- The monad, along with some basic operations

-- A monad with failure (including error messages), collection of
-- constraints, and a reader component (a meta-context).

record Check (c : Constants) (A : Set ℓ) : Set (lsuc a ⊔ ℓ) where
  constructor wrap
  no-eta-equality
  field
    run : Meta-con c → String ⊎ (A × Constraints c)

open Check public

-- Failure.

fail : String → Check c A
fail s .run _ = inj₁ s

-- The meta-context.

ask : Check c (Meta-con c)
ask .run Μ = inj₂ (Μ , none)

-- | If the first computation fails, try the second one. In that case,
-- throw away the first computation's error message.

infixr 2 _catch_

_catch_ : Check c A → Check c A → Check c A
(m₁ catch m₂) .run Μ with m₁ .run Μ
… | inj₁ _     = m₂ .run Μ
… | x@(inj₂ _) = x

-- Registering a constraint.

require : (Contexts c → Set a) → Check c ⊤
require C .run _ = inj₂ (tt , con C)

-- The monad's return operation.

return : A → Check c A
return x .run _ = inj₂ (x , none)

-- The monad's bind operation.

infixl 1 _>>=_

_>>=_ : Check c A → (A → Check c B) → Check c B
(m >>= f) .run Μ with m .run Μ
… | inj₁ s         = inj₁ s
… | inj₂ (x , Cs₁) with f x .run Μ
…   | inj₁ s         = inj₁ s
…   | inj₂ (y , Cs₂) = inj₂ (y , Cs₁ ∪′ Cs₂)

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

-- OK x y γ means that the computation x succeeded for γ .metas,
-- returned y, and that the returned constraints are satisfiable with
-- respect to γ.

data OK {A : Set ℓ} (x : Check c A) (y : A) (γ : Contexts c) :
       Set (lsuc a ⊔ ℓ) where
  ok : x .run (γ .metas) PE.≡ inj₂ (y , Cs) → ⟦ Cs ⟧′ γ → OK x y γ

pattern not-ok = ok ()      _
pattern ok!    = ok PE.refl _

opaque

  -- An inversion lemma for _catch_.

  inv-catch : OK (x catch y) z γ → OK x z γ ⊎ OK y z γ
  inv-catch {x} {γ} (ok eq      _)  with x .run (γ .metas) in eq
  inv-catch         (ok PE.refl cs) | inj₂ _ = inj₁ (ok eq cs)
  inv-catch         (ok eq      cs) | inj₁ _ = inj₂ (ok eq cs)

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
  inv->>= {x} {γ} (ok _ _)        with x .run (γ .metas) in eq₁
  inv->>=         not-ok          | inj₁ _
  inv->>= {f} {γ} _               | inj₂ (y , _)   with f y .run
                                                            (γ .metas)
                                                     in eq₂
  inv->>=         not-ok          | _              | inj₁ _
  inv->>=         (ok PE.refl cs) | inj₂ (y , Cs₁) | inj₂ (_ , Cs₂) =
    let cs₁ , cs₂ = ⟦∪⟧′⇔⟦∪′⟧′ Cs₁ Cs₂ .proj₂ cs in
    inv y (ok eq₁ cs₁) (ok eq₂ cs₂)

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
