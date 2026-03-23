------------------------------------------------------------------------
-- Raw terms, weakening (renaming) and substitution.
------------------------------------------------------------------------

module Definition.Untyped {a} (M : Set a) where

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
open import Tools.List
import Tools.PropositionalEquality as PE
open import Tools.Relation as Dec

-- Some definitions that do not depend on M are re-exported from
-- Definition.Untyped.NotParametrised.

open import Definition.Untyped.NotParametrised public

private
  variable
    m m₁ m₂ n o o₁ o₂ : Nat
    x₁ x₂ : Fin _
    ks ks′ : List _
    k : Term-kind

infix 30 ΠΣ⟨_⟩_,_▷_▹_
infix 30 Π_,_▷_▹_
infix 30 Σ_,_▷_▹_
infix 30 Σˢ_,_▷_▹_
infix 30 Σʷ_,_▷_▹_
infix 30 Σ⟨_⟩_,_▷_▹_
infixl 30 _∘⟨_⟩_
infixl 30 _∘_
infix 30 ⟦_⟧_▹_
infixl 30 _ₛ•ₛ_ _•ₛ_ _ₛ•_
infixr 30 _supᵘ_ _supᵘₗ′_
infix 25 _[_] _[_]′
infix 25 _[_]₀
infix 25 _[_]↑
infix 25 _[_,_]₁₀
infix 25 _[_]↑²
infix 25 _[_][_]↑
infix 24 _∙[_][_][_]ʷ _∙[_][_][_]

------------------------------------------------------------------------
-- The syntax

mutual

  -- Terms.

  Term : Nat → Set a
  Term = Term[ tm ]

  -- Levels.

  Lvl : Nat → Set a
  Lvl = Term[ lvl ]

  -- There are two kinds of terms: regular terms and universe levels.
  -- Universe levels are either "ω + m" or regular terms.
  --
  -- The type of terms is indexed by the number of free variables.
  -- Variables are de Bruijn indices.
  --
  -- Names of definitions are de Bruijn levels. Terms are currently not
  -- parametrised by the number of names, but it might make sense to do
  -- so: currently a predicate Names< is used in parts of the
  -- development, and at least some uses of this predicate could
  -- presumably be avoided if terms were parametrised by the number of
  -- names.

  data Term[_] : Term-kind → Nat → Set a where
    var          : (x : Fin n) → Term n
    defn         : (α : Nat) → Term n
    Level        : Term n
    zeroᵘ        : Term n
    sucᵘ         : Term n → Term n
    _supᵘ_       : Term n → Term n → Term n
    ωᵘ+          : (m : Nat) → Lvl n
    level        : (t : Term n) → Lvl n
    U            : Lvl n → Term n
    Lift         : (l : Lvl n) (A : Term n) → Term n
    lift         : (a : Term n) → Term n
    lower        : (a : Term n) → Term n
    Empty        : Term n
    emptyrec     : (p : M) (A t : Term n) → Term n
    Unit         : (s : Strength) → Term n
    star         : (s : Strength) → Term n
    unitrec      : (p q : M) (A : Term (1+ n)) (t u : Term n) → Term n
    ΠΣ⟨_⟩_,_▷_▹_ : (b : BinderMode) (p q : M) (A : Term n)
                   (B : Term (1+ n)) → Term n
    lam          : (p : M) (t : Term (1+ n)) → Term n
    _∘⟨_⟩_       : (t : Term n) (p : M) (u : Term n) → Term n
    prod         : (s : Strength) (p : M) (t u : Term n) → Term n
    fst          : (p : M) (t : Term n) → Term n
    snd          : (p : M) (t : Term n) → Term n
    prodrec      : (r p q : M) (A : Term (1+ n)) (t : Term n)
                   (u : Term (2+ n)) → Term n
    ℕ            : Term n
    zero         : Term n
    suc          : (t : Term n) → Term n
    natrec       : (p q r : M) (A : Term (1+ n)) (t : Term n)
                   (u : Term (2+ n)) (v : Term n) → Term n
    Id           : (A t u : Term n) → Term n
    rfl          : Term n
    J            : (p q : M) (A t : Term n) (B : Term (2+ n))
                   (u v w : Term n) → Term n
    K            : (p : M) (A t : Term n) (B : Term (1+ n))
                   (u v : Term n) → Term n
    []-cong      : (s : Strength) (l : Lvl n) (A t u v : Term n) →
                   Term n

pattern zeroᵘₗ = level zeroᵘ
pattern U₀     = U zeroᵘₗ

pattern Unit! = Unit _
pattern Unitʷ = Unit 𝕨
pattern Unitˢ = Unit 𝕤

pattern Π_,_▷_▹_ p q F G = ΠΣ⟨ BMΠ ⟩ p , q ▷ F ▹ G
pattern Σˢ_,_▷_▹_ p q F G = ΠΣ⟨ BMΣ 𝕤 ⟩ p , q ▷ F ▹ G
pattern Σʷ_,_▷_▹_ p q F G = ΠΣ⟨ BMΣ 𝕨 ⟩ p , q ▷ F ▹ G
pattern Σ_,_▷_▹_ p q F G = ΠΣ⟨ BMΣ _ ⟩ p , q ▷ F ▹ G
pattern Σ⟨_⟩_,_▷_▹_ s p q F G = ΠΣ⟨ BMΣ s ⟩ p , q ▷ F ▹ G

pattern _∘_ t u = t ∘⟨ _ ⟩ u

pattern prodˢ p t u = prod 𝕤 p t u
pattern prodʷ p t u = prod 𝕨 p t u
pattern prod! t u = prod _ _ t u

pattern star! = star _
pattern starʷ = star 𝕨
pattern starˢ = star 𝕤

pattern []-cong! l A t u v = []-cong _ l A t u v
pattern []-congʷ l A t u v = []-cong 𝕨 l A t u v
pattern []-congˢ l A t u v = []-cong 𝕤 l A t u v

private variable
  t : Term[ _ ] _
  l : Lvl _

-- Pairs of definition contexts and variable contexts.

Cons : (_ _ : Nat) → Set a
Cons = Context-pair Term

-- Type constructors.

data BindingType : Set a where
  BM : BinderMode → (p q : M) → BindingType

pattern BΠ p q = BM BMΠ p q
pattern BΠ! = BΠ _ _
pattern BΣ s p q = BM (BMΣ s) p q
pattern BΣ! = BΣ _ _ _
pattern BΣʷ = BΣ 𝕨 _ _
pattern BΣˢ = BΣ 𝕤 _ _

⟦_⟧_▹_ : BindingType → Term n → Term (1+ n) → Term n
⟦ BM b p q ⟧ A ▹ B = ΠΣ⟨ b ⟩ p , q ▷ A ▹ B

-- Fully normalized natural numbers

data Numeral {n : Nat} : Term n → Set a where
  zeroₙ : Numeral zero
  sucₙ : Numeral t → Numeral (suc t)

-- The canonical term corresponding to the given natural number.

sucⁿ : Nat → Term n
sucⁿ 0      = zero
sucⁿ (1+ n) = suc (sucⁿ n)

-- Infinite level literals.

data Infinite {n} : Term[ k ] n → Set a where
  ωᵘ+ : Infinite (ωᵘ+ m)

-- Level literals.

data Level-literal {n : Nat} : Term[ k ] n → Set a where
  zeroᵘ : Level-literal zeroᵘ
  sucᵘ  : Level-literal t → Level-literal (sucᵘ t)
  ωᵘ+   : Level-literal (ωᵘ+ m)
  level : Level-literal t → Level-literal (level t)

opaque

  -- One can decide whether a term is a level literal or not.

  Level-literal? : (t : Term[ k ] n) → Dec (Level-literal t)
  Level-literal? = λ where
    zeroᵘ    → yes zeroᵘ
    (sucᵘ t) →
      Dec.map sucᵘ (λ { (sucᵘ t-lit) → t-lit }) (Level-literal? t)
    (ωᵘ+ _)   → yes ωᵘ+
    (level t) →
      Dec.map level (λ { (level t-lit) → t-lit }) (Level-literal? t)
    (var _)                 → no (λ ())
    (defn _)                → no (λ ())
    Level                   → no (λ ())
    (_ supᵘ _)              → no (λ ())
    (U _)                   → no (λ ())
    (Lift _ _)              → no (λ ())
    (lift _)                → no (λ ())
    (lower _)               → no (λ ())
    Empty                   → no (λ ())
    (emptyrec _ _ _)        → no (λ ())
    (Unit _)                → no (λ ())
    (star _)                → no (λ ())
    (unitrec _ _ _ _ _)     → no (λ ())
    (ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _) → no (λ ())
    (lam _ _)               → no (λ ())
    (_ ∘⟨ _ ⟩ _)            → no (λ ())
    (prod _ _ _ _)          → no (λ ())
    (fst _ _)               → no (λ ())
    (snd _ _)               → no (λ ())
    (prodrec _ _ _ _ _ _)   → no (λ ())
    ℕ                       → no (λ ())
    zero                    → no (λ ())
    (suc _)                 → no (λ ())
    (natrec _ _ _ _ _ _ _)  → no (λ ())
    (Id _ _ _)              → no (λ ())
    rfl                     → no (λ ())
    (J _ _ _ _ _ _ _ _)     → no (λ ())
    (K _ _ _ _ _ _)         → no (λ ())
    ([]-cong _ _ _ _ _ _)   → no (λ ())

opaque

  -- Converts level literals that are terms to the corresponding
  -- natural numbers.

  size-of-Level : {t : Term n} → Level-literal t → Nat
  size-of-Level zeroᵘ        = 0
  size-of-Level (sucᵘ t-lit) = 1+ (size-of-Level t-lit)

opaque
  unfolding size-of-Level

  -- Converts level literals to universe levels.

  Level-literal→Universe-level : Level-literal l → Universe-level
  Level-literal→Universe-level (ωᵘ+ {m})     = ωᵘ+ m
  Level-literal→Universe-level (level t-lit) = 0ᵘ+ (size-of-Level t-lit)

-- A successor function for levels.

1ᵘ+ : Term[ k ] n → Term[ k ] n
1ᵘ+ {k = tm} t         = sucᵘ t
1ᵘ+          (ωᵘ+ m)   = ωᵘ+ (1+ m)
1ᵘ+          (level t) = level (sucᵘ t)

-- Iterated applications of 1ᵘ+.

1ᵘ+ⁿ : Nat → Term[ k ] n → Term[ k ] n
1ᵘ+ⁿ 0      t = t
1ᵘ+ⁿ (1+ n) t = 1ᵘ+ (1ᵘ+ⁿ n t)

opaque

  -- The canonical level term corresponding to the given natural number.

  ↓ᵘ_ : Nat → Term n
  ↓ᵘ k = 1ᵘ+ⁿ k zeroᵘ

opaque

  -- A variant of _supᵘ_.
  --
  -- If the inputs are level literals, then a literal is returned.

  _supᵘₗ′_ : Term n → Term n → Term n
  l₁ supᵘₗ′ l₂ with Level-literal? l₁ ×-dec Level-literal? l₂
  … | yes (l₁-lit , l₂-lit) =
    ↓ᵘ (size-of-Level l₁-lit ⊔ size-of-Level l₂-lit)
  … | no _ =
    l₁ supᵘ l₂

------------------------------------------------------------------------
-- An alternative syntax representation

-- Arguments can be regular terms or levels, in each case binding a
-- certain number of arguments.

Arg-kind : Set
Arg-kind = Term-kind × Nat

-- Some abbreviations.

tmᵃ : Nat → Arg-kind
tmᵃ = tm ,_

lvlᵃ : Nat → Arg-kind
lvlᵃ = lvl ,_

-- Constructor is indexed by a list of natural numbers specifying the
-- number of sub-terms (the length of the list) and the number of new
-- variables bound by each sub-term (each element in the list).

data Constructor : Term-kind → List Arg-kind → Set a where
  defnᵏ : (α : Nat) → Constructor tm []

  Levelᵏ : Constructor tm []
  zeroᵘᵏ : Constructor tm []
  sucᵘᵏ  : Constructor tm (tmᵃ 0 ∷ [])
  supᵘᵏ  : Constructor tm (tmᵃ 0 ∷ tmᵃ 0 ∷ [])
  ωᵘ+ᵏ   : (m : Nat) → Constructor lvl []
  levelᵏ : Constructor lvl (tmᵃ 0 ∷ [])

  Uᵏ : Constructor tm (lvlᵃ 0 ∷ [])

  Liftᵏ  : Constructor tm (lvlᵃ 0 ∷ tmᵃ 0 ∷ [])
  liftᵏ  : Constructor tm (tmᵃ 0 ∷ [])
  lowerᵏ : Constructor tm (tmᵃ 0 ∷ [])

  Emptyᵏ    : Constructor tm []
  emptyrecᵏ : (p : M) → Constructor tm (tmᵃ 0 ∷ tmᵃ 0 ∷ [])

  Unitᵏ    : Strength → Constructor tm []
  starᵏ    : Strength → Constructor tm []
  unitrecᵏ : (p q : M) → Constructor tm (tmᵃ 1 ∷ tmᵃ 0 ∷ tmᵃ 0 ∷ [])

  ΠΣᵏ : (b : BinderMode) (p q : M) → Constructor tm (tmᵃ 0 ∷ tmᵃ 1 ∷ [])

  lamᵏ : (p : M) → Constructor tm (tmᵃ 1 ∷ [])
  appᵏ : (p : M) → Constructor tm (tmᵃ 0 ∷ tmᵃ 0 ∷ [])

  prodᵏ    : Strength → (p : M) → Constructor tm (tmᵃ 0 ∷ tmᵃ 0 ∷ [])
  fstᵏ     : (p : M) → Constructor tm (tmᵃ 0 ∷ [])
  sndᵏ     : (p : M) → Constructor tm (tmᵃ 0 ∷ [])
  prodrecᵏ : (r p q : M) → Constructor tm (tmᵃ 1 ∷ tmᵃ 0 ∷ tmᵃ 2 ∷ [])

  ℕᵏ      : Constructor tm []
  zeroᵏ   : Constructor tm []
  sucᵏ    : Constructor tm (tmᵃ 0 ∷ [])
  natrecᵏ : (p q r : M) →
            Constructor tm (tmᵃ 1 ∷ tmᵃ 0 ∷ tmᵃ 2 ∷ tmᵃ 0 ∷ [])

  Idᵏ      : Constructor tm (tmᵃ 0 ∷ tmᵃ 0 ∷ tmᵃ 0 ∷ [])
  rflᵏ     : Constructor tm []
  Jᵏ       : M → M →
             Constructor tm
               (tmᵃ 0 ∷ tmᵃ 0 ∷ tmᵃ 2 ∷ tmᵃ 0 ∷ tmᵃ 0 ∷ tmᵃ 0 ∷ [])
  Kᵏ       : M →
             Constructor tm (tmᵃ 0 ∷ tmᵃ 0 ∷ tmᵃ 1 ∷ tmᵃ 0 ∷ tmᵃ 0 ∷ [])
  []-congᵏ : Strength →
             Constructor tm
               (lvlᵃ 0 ∷ tmᵃ 0 ∷ tmᵃ 0 ∷ tmᵃ 0 ∷ tmᵃ 0 ∷ [])

private variable
  c c′ : Constructor _ _

mutual

  -- In the alternative term representation a term is either a
  -- variable (de Bruijn index) or a "generic" term. The parameter is
  -- the number of free variables.
  --
  -- A term con k (n₁ ∷ … ∷ nₘ) contains m arguments (possibly zero),
  -- where argument i binds nᵢ variables.

  data Term[_]′ : Term-kind → Nat → Set a where
    var : (x : Fin n) → Term[ tm ]′ n
    con : (c : Constructor k ks) (ts : Args n ks) → Term[ k ]′ n

  -- Lists of arguments.

  infixr 5 _∷ₜ_

  data Args : Nat → List Arg-kind → Set a where
    []   : Args n []
    _∷ₜ_ : (t : Term[ k ]′ (m + n)) (ts : Args n ks) →
           Args n ((k , m) ∷ ks)

private variable
  ts ts′ : Args _ _

-- Converting from the alternative syntax.

toTerm : Term[ k ]′ n → Term[ k ] n
toTerm (var x) =
  var x
toTerm (con (defnᵏ α) []) =
  defn α
toTerm (con Levelᵏ []) =
  Level
toTerm (con zeroᵘᵏ []) =
  zeroᵘ
toTerm (con sucᵘᵏ (t ∷ₜ [])) =
  sucᵘ (toTerm t)
toTerm (con supᵘᵏ (t₁ ∷ₜ t₂ ∷ₜ [])) =
  toTerm t₁ supᵘ toTerm t₂
toTerm (con (ωᵘ+ᵏ m) []) =
  ωᵘ+ m
toTerm (con levelᵏ (t ∷ₜ [])) =
  level (toTerm t)
toTerm (con Uᵏ (l ∷ₜ [])) =
  U (toTerm l)
toTerm (con Liftᵏ (l ∷ₜ A ∷ₜ [])) =
  Lift (toTerm l) (toTerm A)
toTerm (con liftᵏ (a ∷ₜ [])) =
  lift (toTerm a)
toTerm (con lowerᵏ (a ∷ₜ [])) =
  lower (toTerm a)
toTerm (con Emptyᵏ []) =
  Empty
toTerm (con (emptyrecᵏ p) (A ∷ₜ t ∷ₜ [])) =
  emptyrec p (toTerm A) (toTerm t)
toTerm (con (Unitᵏ s) []) =
  Unit s
toTerm (con (starᵏ s) []) =
  star s
toTerm (con (unitrecᵏ p q) (A ∷ₜ t ∷ₜ u ∷ₜ [])) =
  unitrec p q (toTerm A) (toTerm t)
    (toTerm u)
toTerm (con (ΠΣᵏ b p q) (A ∷ₜ B ∷ₜ [])) =
  ΠΣ⟨ b ⟩ p , q ▷ toTerm A ▹ toTerm B
toTerm (con (lamᵏ p) (t ∷ₜ [])) =
  lam p (toTerm t)
toTerm (con (appᵏ p) (t ∷ₜ u ∷ₜ [])) =
  toTerm t ∘⟨ p ⟩ toTerm u
toTerm (con (prodᵏ s p) (t ∷ₜ u ∷ₜ [])) =
  prod s p (toTerm t) (toTerm u)
toTerm (con (fstᵏ p) (t ∷ₜ [])) =
  fst p (toTerm t)
toTerm (con (sndᵏ p) (t ∷ₜ [])) =
  snd p (toTerm t)
toTerm (con (prodrecᵏ r p q) (A ∷ₜ t ∷ₜ u ∷ₜ [])) =
  prodrec r p q (toTerm A) (toTerm t)
    (toTerm u)
toTerm (con ℕᵏ []) =
  ℕ
toTerm (con zeroᵏ []) =
  zero
toTerm (con sucᵏ (t ∷ₜ [])) =
  suc (toTerm t)
toTerm (con (natrecᵏ p q r) (A ∷ₜ z ∷ₜ s ∷ₜ n ∷ₜ [])) =
  natrec p q r (toTerm A) (toTerm z)
    (toTerm s) (toTerm n)
toTerm (con Idᵏ (A ∷ₜ t ∷ₜ u ∷ₜ [])) =
  Id (toTerm A) (toTerm t) (toTerm u)
toTerm (con rflᵏ []) =
  rfl
toTerm (con (Jᵏ p q) (A ∷ₜ t ∷ₜ B ∷ₜ u ∷ₜ v ∷ₜ w ∷ₜ [])) =
  J p q (toTerm A) (toTerm t) (toTerm B)
    (toTerm u) (toTerm v) (toTerm w)
toTerm (con (Kᵏ p) (A ∷ₜ t ∷ₜ B ∷ₜ u ∷ₜ v ∷ₜ [])) =
  K p (toTerm A) (toTerm t) (toTerm B)
    (toTerm u) (toTerm v)
toTerm (con ([]-congᵏ s) (l ∷ₜ A ∷ₜ t ∷ₜ u ∷ₜ v ∷ₜ [])) =
  []-cong s (toTerm l) (toTerm A)
    (toTerm t) (toTerm u) (toTerm v)

mutual

  -- Converting to the alternative syntax.

  fromTerm : Term[ k ] n → Term[ k ]′ n
  fromTerm (var x) =
    var x
  fromTerm (defn α) =
    con (defnᵏ α) []
  fromTerm Level =
    con Levelᵏ []
  fromTerm zeroᵘ =
    con zeroᵘᵏ []
  fromTerm (sucᵘ t) =
    con sucᵘᵏ (fromTerm t ∷ₜ [])
  fromTerm (t₁ supᵘ t₂) =
    con supᵘᵏ (fromTerm t₁ ∷ₜ fromTerm t₂ ∷ₜ [])
  fromTerm (ωᵘ+ m) =
    con (ωᵘ+ᵏ m) []
  fromTerm (level t) =
    con levelᵏ (fromTerm t ∷ₜ [])
  fromTerm (U l) =
    con Uᵏ (fromTerm l ∷ₜ [])
  fromTerm (Lift l A) =
    con Liftᵏ (fromTerm l ∷ₜ fromTerm A ∷ₜ [])
  fromTerm (lift a) =
    con liftᵏ (fromTerm a ∷ₜ [])
  fromTerm (lower a) =
    con lowerᵏ (fromTerm a ∷ₜ [])
  fromTerm (ΠΣ⟨ b ⟩ p , q ▷ A ▹ B) =
    con (ΠΣᵏ b p q) (fromTerm A ∷ₜ fromTerm B ∷ₜ [])
  fromTerm (lam p t) =
    con (lamᵏ p) (fromTerm t ∷ₜ [])
  fromTerm (t ∘⟨ p ⟩ u) =
    con (appᵏ p) (fromTerm t ∷ₜ fromTerm u ∷ₜ [])
  fromTerm (prod s p t u) =
    con (prodᵏ s p) (fromTerm t ∷ₜ fromTerm u ∷ₜ [])
  fromTerm (fst p t) =
    con (fstᵏ p) (fromTerm t ∷ₜ [])
  fromTerm (snd p t) =
    con (sndᵏ p) (fromTerm t ∷ₜ [])
  fromTerm (prodrec r p q A t u) =
    con (prodrecᵏ r p q) (fromTerm A ∷ₜ fromTerm t ∷ₜ fromTerm u ∷ₜ [])
  fromTerm ℕ =
    con ℕᵏ []
  fromTerm zero =
    con zeroᵏ []
  fromTerm (suc t) =
    con sucᵏ (fromTerm t ∷ₜ [])
  fromTerm (natrec p q r A z s n) =
    con (natrecᵏ p q r)
      (fromTerm A ∷ₜ fromTerm z ∷ₜ fromTerm s ∷ₜ fromTerm n ∷ₜ [])
  fromTerm (Unit s) =
    con (Unitᵏ s) []
  fromTerm (star s) =
    con (starᵏ s) []
  fromTerm (unitrec p q A t u) =
    con (unitrecᵏ p q) (fromTerm A ∷ₜ fromTerm t ∷ₜ fromTerm u ∷ₜ [])
  fromTerm Empty =
    con Emptyᵏ []
  fromTerm (emptyrec p A t) =
    con (emptyrecᵏ p) (fromTerm A ∷ₜ fromTerm t ∷ₜ [])
  fromTerm (Id A t u) =
    con Idᵏ (fromTerm A ∷ₜ fromTerm t ∷ₜ fromTerm u ∷ₜ [])
  fromTerm rfl =
    con rflᵏ []
  fromTerm (J p q A t B u v w) =
    con (Jᵏ p q)
      (fromTerm A ∷ₜ fromTerm t ∷ₜ fromTerm B ∷ₜ fromTerm u ∷ₜ
       fromTerm v ∷ₜ fromTerm w ∷ₜ [])
  fromTerm (K p A t B u v) =
    con (Kᵏ p)
      (fromTerm A ∷ₜ fromTerm t ∷ₜ fromTerm B ∷ₜ fromTerm u ∷ₜ
       fromTerm v ∷ₜ [])
  fromTerm ([]-cong s l A t u v) =
    con ([]-congᵏ s)
      (fromTerm l ∷ₜ fromTerm A ∷ₜ fromTerm t ∷ₜ fromTerm u ∷ₜ
       fromTerm v ∷ₜ [])

------------------------------------------------------------------------
-- Weakening

-- Weakening of terms.
-- If η : Γ ≤ Δ and Δ ⊢ t : A then Γ ⊢ wkₜ η t : wkₜ η A.

wk : Wk m n → Term[ k ] n → Term[ k ] m
wk ρ (var x) = var (wkVar ρ x)
wk ρ (defn α) = defn α
wk ρ Level = Level
wk ρ zeroᵘ = zeroᵘ
wk ρ (sucᵘ t) = sucᵘ (wk ρ t)
wk ρ (t₁ supᵘ t₂) = wk ρ t₁ supᵘ wk ρ t₂
wk _ (ωᵘ+ m) = ωᵘ+ m
wk ρ (level t) = level (wk ρ t)
wk ρ (U l) = U (wk ρ l)
wk ρ (Lift l A) = Lift (wk ρ l) (wk ρ A)
wk ρ (lift a) = lift (wk ρ a)
wk ρ (lower a) = lower (wk ρ a)
wk ρ (ΠΣ⟨ b ⟩ p , q ▷ A ▹ B) =
  ΠΣ⟨ b ⟩ p , q ▷ wk ρ A ▹ wk (lift ρ) B
wk ρ (lam p t) = lam p (wk (lift ρ) t)
wk ρ (t ∘⟨ p ⟩ u) = wk ρ t ∘⟨ p ⟩ wk ρ u
wk ρ (prod s p t u) = prod s p (wk ρ t) (wk ρ u)
wk ρ (fst p t) = fst p (wk ρ t)
wk ρ (snd p t) = snd p (wk ρ t)
wk ρ (prodrec r p q A t u) =
  prodrec r p q (wk (lift ρ) A) (wk ρ t) (wk (liftn ρ 2) u)
wk ρ ℕ = ℕ
wk ρ zero = zero
wk ρ (suc t) = suc (wk ρ t)
wk ρ (natrec p q r A z s n) =
  natrec p q r (wk (lift ρ) A) (wk ρ z) (wk (liftn ρ 2) s) (wk ρ n)
wk ρ (Unit s) = Unit s
wk ρ (star s) = star s
wk ρ (unitrec p q A t u) =
  unitrec p q (wk (lift ρ) A) (wk ρ t) (wk ρ u)
wk ρ Empty = Empty
wk ρ (emptyrec p A t) = emptyrec p (wk ρ A) (wk ρ t)
wk ρ (Id A t u) = Id (wk ρ A) (wk ρ t) (wk ρ u)
wk ρ rfl = rfl
wk ρ (J p q A t B u v w) =
  J p q (wk ρ A) (wk ρ t) (wk (liftn ρ 2) B) (wk ρ u) (wk ρ v) (wk ρ w)
wk ρ (K p A t B u v) =
  K p (wk ρ A) (wk ρ t) (wk (lift ρ) B) (wk ρ u) (wk ρ v)
wk ρ ([]-cong s l A t u v) =
  []-cong s (wk ρ l) (wk ρ A) (wk ρ t) (wk ρ u) (wk ρ v)

-- Weakening for the alternative term representation.

mutual

  wk′ : Wk m n → Term[ k ]′ n → Term[ k ]′ m
  wk′ ρ (var x)    = var (wkVar ρ x)
  wk′ ρ (con k ts) = con k (wkArgs ρ ts)

  wkArgs : {as : List Arg-kind} → Wk m n → Args n as → Args m as
  wkArgs ρ []              = []
  wkArgs ρ (_∷ₜ_ {m} t ts) = wk′ (liftn ρ m) t ∷ₜ wkArgs ρ ts

-- Adding one variable to the context requires wk1.
-- If Γ ⊢ t : B then Γ∙A ⊢ wk1 t : wk1 B.

wk1 : Term[ k ] n → Term[ k ] (1+ n)
wk1 = wk (step id)

-- Two successive uses of wk1.

wk2 : Term[ k ] n → Term[ k ] (1+ (1+ n))
wk2 = wk1 ∘→ wk1

-- An alternative to wk2.

wk₂ : Term[ k ] n → Term[ k ] (2+ n)
wk₂ = wk (step (step id))

-- The function wk[ k ] applies wk1 k times.

wk[_] : ∀ m → Term[ k ] n → Term[ k ] (m + n)
wk[ 0    ] t = t
wk[ 1+ k ] t = wk1 (wk[ k ] t)

-- An alternative to wk[_].

wk[_]′ : ∀ m → Term[ k ] n → Term[ k ] (m + n)
wk[ k ]′ = wk (stepn id k)

-- Δ ∙[ k ][ Γ ][ ρ ]ʷ is Δ extended with the last k elements of Γ,
-- modified using ρ (suitably lifted).

_∙[_][_][_]ʷ :
  Con Term m → ∀ k → Con Term (k + n) → Wk m n → Con Term (k + m)
Δ ∙[ 0    ][ _     ][ _ ]ʷ = Δ
Δ ∙[ 1+ k ][ Γ ∙ A ][ ρ ]ʷ = Δ ∙[ k ][ Γ ][ ρ ]ʷ ∙ wk (liftn ρ k) A

------------------------------------------------------------------------
-- Substitution

-- The substitution operation t [ σ ] replaces the free de Bruijn
-- indices of term t by chosen terms as specified by σ.

-- The substitution σ itself is a map from Fin n to terms.

Subst : Nat → Nat → Set a
Subst m n = Fin n → Term m

-- Given closed contexts ⊢ Γ and ⊢ Δ,
-- substitutions may be typed via Γ ⊢ σ : Δ meaning that
-- Γ ⊢ σ(x) : (subst σ Δ)(x) for all x ∈ dom(Δ).
--
-- The substitution operation is then typed as follows:
-- If Γ ⊢ σ : Δ and Δ ⊢ t : A, then Γ ⊢ t [ σ ] : A [ σ ].
--
-- Although substitutions are untyped, typing helps us
-- to understand the operation on substitutions.

-- We may view σ as the finite stream σ 0, σ 1, ..., σ n

-- Extract the substitution of the first variable.
--
-- If Γ ⊢ σ : Δ∙A  then Γ ⊢ head σ : A [ σ ].

head : Subst m (1+ n) → Term m
head σ = σ x0

-- Remove the first variable instance of a substitution
-- and shift the rest to accommodate.
--
-- If Γ ⊢ σ : Δ∙A then Γ ⊢ tail σ : Δ.

tail : Subst m (1+ n) → Subst m n
tail σ x = σ (x +1)

-- A generalisation of tail.

tail[_] : ∀ k → Subst m (k + n) → Subst m n
tail[ 0    ] σ = σ
tail[ 1+ k ] σ = tail[ k ] (tail σ)

-- Substitution of a variable.
--
-- If Γ ⊢ σ : Δ then Γ ⊢ substVar σ x : (subst σ Δ)(x).

substVar : (σ : Subst m n) (x : Fin n) → Term m
substVar σ x = σ x

-- Identity substitution.
-- Replaces each variable by itself.
--
-- Γ ⊢ idSubst : Γ.

idSubst : Subst n n
idSubst = var

-- Weaken a substitution by one.
--
-- If Γ ⊢ σ : Δ then Γ∙A ⊢ wk1Subst σ : Δ.

wk1Subst : Subst m n → Subst (1+ m) n
wk1Subst σ x = wk1 (σ x)

-- An n-ary variant of wk1Subst.

wkSubst : ∀ k → Subst m n → Subst (k + m) n
wkSubst 0      = idᶠ
wkSubst (1+ k) = wk1Subst ∘→ wkSubst k

-- Substitution analogue to wk₀.

wkSubst₀ : Subst n 0
wkSubst₀ ()

-- Lift a substitution.
--
-- If Γ ⊢ σ : Δ then Γ∙A ⊢ liftSubst σ : Δ∙A.

liftSubst : (σ : Subst m n) → Subst (1+ m) (1+ n)
liftSubst σ x0     = var x0
liftSubst σ (x +1) = wk1Subst σ x

liftSubstn : {k m : Nat} → Subst k m → (n : Nat) → Subst (n + k) (n + m)
liftSubstn σ Nat.zero = σ
liftSubstn σ (1+ n)   = liftSubst (liftSubstn σ n)

-- A synonym of liftSubst.

_⇑ : Subst m n → Subst (1+ m) (1+ n)
_⇑ = liftSubst

-- A synonym of liftSubstn.

_⇑[_] : Subst m n → ∀ k → Subst (k + m) (k + n)
_⇑[_] = liftSubstn

-- Transform a weakening into a substitution.
--
-- If ρ : Γ ≤ Δ then Γ ⊢ toSubst ρ : Δ.

toSubst :  Wk m n → Subst m n
toSubst pr x = var (wkVar pr x)

-- Apply a substitution to a term.
--
-- If Γ ⊢ σ : Δ and Δ ⊢ t : A then Γ ⊢ t [ σ ] : A [ σ ].

_[_] : (t : Term[ k ] n) (σ : Subst m n) → Term[ k ] m
var x [ σ ] = σ x
defn α [ σ ] = defn α
Level [ σ ] = Level
zeroᵘ [ σ ] = zeroᵘ
sucᵘ t [ σ ] = sucᵘ (t [ σ ])
t₁ supᵘ t₂ [ σ ] = (t₁ [ σ ]) supᵘ (t₂ [ σ ])
ωᵘ+ m [ _ ] = ωᵘ+ m
level t [ σ ] = level (t [ σ ])
U l [ σ ] = U (l [ σ ])
Lift l A [ σ ] = Lift (l [ σ ]) (A [ σ ])
lift a [ σ ] = lift (a [ σ ])
lower a [ σ ] = lower (a [ σ ])
ΠΣ⟨ b ⟩ p , q ▷ A ▹ B [ σ ] =
  ΠΣ⟨ b ⟩ p , q ▷ A [ σ ] ▹ (B [ σ ⇑ ])
lam p t [ σ ] = lam p (t [ σ ⇑ ])
t ∘⟨ p ⟩ u [ σ ] = (t [ σ ]) ∘⟨ p ⟩ (u [ σ ])
prod s p t u [ σ ] = prod s p (t [ σ ]) (u [ σ ])
fst p t [ σ ] = fst p (t [ σ ])
snd p t [ σ ] = snd p (t [ σ ])
prodrec r p q A t u [ σ ] =
  prodrec r p q (A [ σ ⇑ ]) (t [ σ ]) (u [ σ ⇑[ 2 ] ])
ℕ [ σ ] = ℕ
zero [ σ ] = zero
suc t [ σ ] = suc (t [ σ ])
natrec p q r A z s n [ σ ] =
  natrec p q r (A [ σ ⇑ ]) (z [ σ ]) (s [ σ ⇑[ 2 ] ]) (n [ σ ])
Unit s [ σ ] = Unit s
star s [ σ ] = star s
unitrec p q A t u [ σ ] =
  unitrec p q (A [ σ ⇑ ]) (t [ σ ]) (u [ σ ])
Empty [ σ ] = Empty
emptyrec p A t [ σ ] = emptyrec p (A [ σ ]) (t [ σ ])
Id A t u [ σ ] = Id (A [ σ ]) (t [ σ ]) (u [ σ ])
rfl [ σ ] = rfl
J p q A t B u v w [ σ ] =
  J p q (A [ σ ]) (t [ σ ]) (B [ σ ⇑[ 2 ] ]) (u [ σ ]) (v [ σ ])
    (w [ σ ])
K p A t B u v [ σ ] =
  K p (A [ σ ]) (t [ σ ]) (B [ σ ⇑ ]) (u [ σ ]) (v [ σ ])
[]-cong s l A t u v [ σ ] =
  []-cong s (l [ σ ]) (A [ σ ]) (t [ σ ]) (u [ σ ]) (v [ σ ])

-- Substitution for the alternative term representation.

mutual

  _[_]′ : (t : Term[ k ]′ n) (σ : Subst m n) → Term[ k ]′ m
  var x    [ σ ]′ = fromTerm (σ x)
  con k ts [ σ ]′ = con k (substArgs ts σ)

  substArgs : {as : List Arg-kind} → Args n as → Subst m n → Args m as
  substArgs []              σ = []
  substArgs (_∷ₜ_ {m} t ts) σ = t [ σ ⇑[ m ] ]′ ∷ₜ substArgs ts σ

-- Extend a substitution by adding a term as
-- the first variable substitution and shift the rest.
--
-- If Γ ⊢ σ : Δ and Γ ⊢ t : A [ σ ] then Γ ⊢ consSubst σ t : Δ∙A.

consSubst : Subst m n → Term m → Subst m (1+ n)
consSubst σ t  x0    = t
consSubst σ t (x +1) = σ x

-- Singleton substitution.
--
-- If Γ ⊢ t : A then Γ ⊢ sgSubst t : Γ∙A.

sgSubst : Term n → Subst n (1+ n)
sgSubst = consSubst idSubst

-- The substitution ⟨ x ≔ t ⟩ replaces x with t (suitably weakened).

⟨_≔_⟩ : (x : Fin n) → Term (pred n ∸ toℕ x) → Subst (pred n) n
⟨ x0                ≔ t ⟩ = sgSubst t
⟨ _+1 {n = 1+ _} x  ≔ t ⟩ = ⟨ x ≔ t ⟩ ⇑
⟨ _+1 {n = 0}    () ≔ _ ⟩

-- The substitution ⟨ x ≔ t ⟩ replaces x with t (suitably weakened).
-- The variable x can appear in t.

⟨_≔_⟩↑ : (x : Fin n) → Term (n ∸ toℕ x) → Subst n n
⟨ x0                ≔ t ⟩↑ = consSubst (wk1Subst idSubst) t
⟨ _+1 {n = 1+ _} x  ≔ t ⟩↑ = ⟨ x ≔ t ⟩↑ ⇑
⟨ _+1 {n = 0}    () ≔ _ ⟩↑

-- Compose two substitutions.
--
-- If Γ ⊢ σ : Δ and Δ ⊢ σ′ : Φ then Γ ⊢ σ ₛ•ₛ σ′ : Φ.

_ₛ•ₛ_ : Subst m n → Subst n o → Subst m o
_ₛ•ₛ_ σ σ′ x = σ′ x [ σ ]

-- Composition of weakening and substitution.
--
--  If ρ : Γ ≤ Δ and Δ ⊢ σ : Φ then Γ ⊢ ρ •ₛ σ : Φ.

_•ₛ_ : Wk m n → Subst n o → Subst m o
_•ₛ_ ρ σ x = wk ρ (σ x)

--  If Γ ⊢ σ : Δ and ρ : Δ ≤ Φ then Γ ⊢ σ ₛ• ρ : Φ.

_ₛ•_ : Subst m n → Wk n o → Subst m o
_ₛ•_ σ ρ x = σ (wkVar ρ x)

-- The family of substitutions used in _[_]↑, _[_]↑² and _[_][_]↑.

replace₁ : ∀ k → Term (k + n) → Subst (k + n) (1+ n)
replace₁ k t = consSubst (wkSubst k idSubst) t

opaque

  -- A variant of the family of substitutions used in _[_]↑.

  replace₂ : Term (2+ n) → Term (2+ n) → Subst (2+ n) (2+ n)
  replace₂ t u = consSubst (consSubst (wkSubst 2 idSubst) t) u

-- Substitute the first variable of a term with an other term.
--
-- If Γ∙A ⊢ t : B and Γ ⊢ s : A then Γ ⊢ t[s]₀ : B[s]₀.

_[_]₀ : (t : Term[ k ] (1+ n)) (s : Term n) → Term[ k ] n
t [ s ]₀ = t [ sgSubst s ]

-- Substitute the first variable of a term with an other term,
-- but let the two terms share the same context.
--
-- If Γ∙A ⊢ t : B and Γ∙A ⊢ s : A then Γ∙A ⊢ t[s]↑ : B[s]↑.

_[_]↑ : (t : Term[ k ] (1+ n)) (s : Term (1+ n)) → Term[ k ] (1+ n)
t [ s ]↑ = t [ replace₁ 1 s ]


-- Substitute the first two variables of a term with other terms.
--
-- If Γ∙A∙B ⊢ t : C, Γ ⊢ s : A and Γ ⊢ s′ : B then Γ ⊢ t[s,s′] : C[s,s′]

_[_,_]₁₀ : (t : Term[ k ] (2+ n)) (s s′ : Term n) → Term[ k ] n
t [ s , s′ ]₁₀ = t [ consSubst (sgSubst s) s′ ]

-- Substitute the first variable with a term and shift remaining
-- variables up by one
-- If Γ ∙ A ⊢ t : A′ and Γ ∙ B ∙ C ⊢ s : A then Γ ∙ B ∙ C ⊢ t[s]↑² : A′

_[_]↑² : (t : Term[ k ] (1+ n)) (s : Term (2+ n)) → Term[ k ] (2+ n)
t [ s ]↑² = t [ replace₁ 2 s ]

-- A generalisation of _[_]↑ and _[_]↑².

_[_][_]↑ : Term[ k ] (1+ n) → ∀ m → Term (m + n) → Term[ k ] (m + n)
t [ k ][ u ]↑ = t [ replace₁ k u ]

-- Δ ∙[ k ][ Γ ][ σ ] is Δ extended with the last k elements of Γ,
-- modified using σ (suitably lifted).

_∙[_][_][_] :
  Con Term m → ∀ k → Con Term (k + n) → Subst m n → Con Term (k + m)
Δ ∙[ 0    ][ _     ][ _ ] = Δ
Δ ∙[ 1+ k ][ Γ ∙ A ][ σ ] = Δ ∙[ k ][ Γ ][ σ ] ∙ A [ σ ⇑[ k ] ]

------------------------------------------------------------------------
-- Inlining of definitions

opaque

  mutual

    -- The term at the given position, with the definition context
    -- inlined. Opacity is ignored.

    inline-< : DExt (Term 0) m₂ m₁ → m₁ ≤ n → n <′ m₂ → Term 0
    inline-< idᵉ m≤n n<m =
      ⊥-elim (n≮n _ (≤-trans (<′⇒< n<m) m≤n))
    inline-< (step ξ _ _ t) _ (≤′-reflexive _) =
      inline ξ t
    inline-< (step ξ _ _ _) m₁≤n (≤′-step n<m₂) =
      inline-< ξ m₁≤n n<m₂

    -- The term at the given position, if any, with the definition
    -- context inlined. If the number, α, is out of bounds, then
    -- defn α is returned. Opacity is ignored.

    inline-Nat : DExt (Term 0) m₂ m₁ → Nat → Term 0
    inline-Nat {m₂} {m₁} ξ α =
      case m₁ ≤? α of λ where
        (no _)    → defn α
        (yes m₁≤α) →
          case α <′? m₂ of λ where
            (no _)     → defn α
            (yes α<m₂) → inline-< ξ m₁≤α α<m₂

    -- Inlines all definitions that are in scope. Opacity is ignored.

    inline : DExt (Term 0) m₂ m₁ → Term[ k ] n → Term[ k ] n
    inline _ t@(var _) =
      t
    inline ξ (defn α) =
      wk wk₀ (inline-Nat ξ α)
    inline _ t@Level =
      t
    inline _ t@zeroᵘ =
      t
    inline ξ (sucᵘ t) =
      sucᵘ (inline ξ t)
    inline ξ (t supᵘ u) =
      inline ξ t supᵘ inline ξ u
    inline _ (ωᵘ+ m) =
      ωᵘ+ m
    inline ξ (level t) =
      level (inline ξ t)
    inline ξ (U l) =
      U (inline ξ l)
    inline ξ (Lift l A) =
      Lift (inline ξ l) (inline ξ A)
    inline ξ (lift t) =
      lift (inline ξ t)
    inline ξ (lower t) =
      lower (inline ξ t)
    inline ξ (ΠΣ⟨ b ⟩ p , q ▷ A ▹ B) =
      ΠΣ⟨ b ⟩ p , q ▷ inline ξ A ▹ inline ξ B
    inline ξ (lam p t) =
      lam p (inline ξ t)
    inline ξ (t ∘⟨ p ⟩ u) =
      inline ξ t ∘⟨ p ⟩ inline ξ u
    inline ξ (prod s p t u) =
      prod s p (inline ξ t) (inline ξ u)
    inline ξ (fst p t) =
      fst p (inline ξ t)
    inline ξ (snd p t) =
      snd p (inline ξ t)
    inline ξ (prodrec r p q A t u) =
      prodrec r p q (inline ξ A) (inline ξ t) (inline ξ u)
    inline _ t@ℕ =
      t
    inline _ t@zero =
      t
    inline ξ (suc t) =
      suc (inline ξ t)
    inline ξ (natrec p q r A t u v) =
      natrec p q r (inline ξ A) (inline ξ t) (inline ξ u) (inline ξ v)
    inline _ t@(Unit _) =
      t
    inline _ t@(star _) =
      t
    inline ξ (unitrec p q A t u) =
      unitrec p q (inline ξ A) (inline ξ t) (inline ξ u)
    inline _ t@Empty =
      t
    inline ξ (emptyrec p A t) =
      emptyrec p (inline ξ A) (inline ξ t)
    inline ξ (Id A t u) =
      Id (inline ξ A) (inline ξ t) (inline ξ u)
    inline _ t@rfl =
      t
    inline ξ (J p q A t B u v w) =
      J p q (inline ξ A) (inline ξ t) (inline ξ B) (inline ξ u)
        (inline ξ v) (inline ξ w)
    inline ξ (K p A t B u v) =
      K p (inline ξ A) (inline ξ t) (inline ξ B) (inline ξ u) (inline ξ v)
    inline ξ ([]-cong s l A t u v) =
      []-cong s (inline ξ l) (inline ξ A) (inline ξ t) (inline ξ u)
        (inline ξ v)

  -- Inlines all definitions that are in scope. Opacity is ignored.

  inline-Con : DExt (Term 0) m₂ m₁ → Con Term n → Con Term n
  inline-Con _ ε       = ε
  inline-Con ξ (Γ ∙ A) = inline-Con ξ Γ ∙ inline ξ A

  -- Inlines all definitions that are in scope. Opacity is ignored.

  inline-Subst : DExt (Term 0) o₂ o₁ → Subst m n → Subst m n
  inline-Subst ξ σ = inline ξ ∘→ σ

opaque
  unfolding inline as-DExt

  -- A variant of inline for DCon.

  inlineᵈ : DCon (Term 0) n → Term[ k ] m → Term[ k ] m
  inlineᵈ = inline ∘→ as-DExt

  -- A variant of inline-Con for DCon.

  inline-Conᵈ : DCon (Term 0) n → Con Term m → Con Term m
  inline-Conᵈ = inline-Con ∘→ as-DExt

  -- A variant of inline-Subst for DCon.

  inline-Substᵈ : DCon (Term 0) o → Subst m n → Subst m n
  inline-Substᵈ = inline-Subst ∘→ as-DExt

------------------------------------------------------------------------
-- Some inversion lemmas

-- Inversion of equality for Term[_]′.var.

var-cong⁻¹ : Term[_]′.var x₁ PE.≡ var x₂ → x₁ PE.≡ x₂
var-cong⁻¹ PE.refl = PE.refl

-- Inversion of equality for con.

con-cong⁻¹ :
  con {ks = ks} c ts PE.≡ con {ks = ks′} c′ ts′ →
  ∃ λ (eq : ks PE.≡ ks′) →
    PE.subst (Constructor k) eq c PE.≡ c′ ×
    PE.subst (Args _) eq ts PE.≡ ts′
con-cong⁻¹ PE.refl = PE.refl , PE.refl , PE.refl

-- Inversion of equality for _∷ₜ_.

∷-cong⁻¹ :
  {t t′ : Term[ k ]′ (m + n)} →
  _∷ₜ_ {m = m} t ts PE.≡ t′ ∷ₜ ts′ →
  t PE.≡ t′ × ts PE.≡ ts′
∷-cong⁻¹ PE.refl = PE.refl , PE.refl

------------------------------------------------------------------------
-- The type Judgement

-- A type that combines some of the arguments of different kinds of
-- judgements. See Definition.Typed._⊢[_].

data Judgement (n : Nat) : Set a where
  [ctxt]      :                    Judgement n
  [_type]     : (A : Term n)     → Judgement n
  [_≡_type]   : (A B : Term n)   → Judgement n
  [_∷_]       : (t A : Term n)   → Judgement n
  [_≡_∷_]     : (t u A : Term n) → Judgement n
  [_∷Level]   : (l : Lvl n)      → Judgement n
  [_≡_∷Level] : (l₁ l₂ : Lvl n)  → Judgement n

-- A map function for Judgement.

mapJ : (∀ {k} → Term[ k ] m → Term[ k ] n) → Judgement m → Judgement n
mapJ _ [ctxt]            = [ctxt]
mapJ f [ A type]         = [ f A type]
mapJ f [ A ≡ B type]     = [ f A ≡ f B type]
mapJ f [ t ∷ A ]         = [ f t ∷ f A ]
mapJ f [ t ≡ u ∷ A ]     = [ f t ≡ f u ∷ f A ]
mapJ f [ l ∷Level]       = [ f l ∷Level]
mapJ f [ l₁ ≡ l₂ ∷Level] = [ f l₁ ≡ f l₂ ∷Level]

-- Substitution for Judgement.

infix 25 _[_]J

_[_]J : Judgement n → Subst m n → Judgement m
𝓙 [ σ ]J = mapJ _[ σ ] 𝓙

-- A variant of _[_]J.

infix 25 _[_≡_]J

_[_≡_]J : Judgement n → Subst m n → Subst m n → Judgement m
[ctxt]            [ _  ≡ _  ]J = [ctxt]
[ A type]         [ σ₁ ≡ σ₂ ]J = [ A [ σ₁ ] ≡ A [ σ₂ ] type]
[ A ≡ B type]     [ σ₁ ≡ σ₂ ]J = [ A [ σ₁ ] ≡ B [ σ₂ ] type]
[ t ∷ A ]         [ σ₁ ≡ σ₂ ]J = [ t [ σ₁ ] ≡ t [ σ₂ ] ∷ A [ σ₁ ] ]
[ t ≡ u ∷ A ]     [ σ₁ ≡ σ₂ ]J = [ t [ σ₁ ] ≡ u [ σ₂ ] ∷ A [ σ₁ ] ]
[ l ∷Level]       [ σ₁ ≡ σ₂ ]J = [ l [ σ₁ ] ≡ l [ σ₂ ] ∷Level]
[ l₁ ≡ l₂ ∷Level] [ σ₁ ≡ σ₂ ]J = [ l₁ [ σ₁ ] ≡ l₂ [ σ₂ ] ∷Level]
