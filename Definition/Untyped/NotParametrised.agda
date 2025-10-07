------------------------------------------------------------------------
-- Some definitions that are re-exported from Definition.Untyped but
-- do not depend on that module's module parameter
------------------------------------------------------------------------

module Definition.Untyped.NotParametrised where

open import Tools.Fin
open import Tools.Function
open import Tools.Level
open import Tools.List
open import Tools.Nat
open import Tools.PropositionalEquality

private variable
  a       : Level
  α l m n : Nat
  𝕋 𝕌     : Set a
  P Q     : Nat → Set _

------------------------------------------------------------------------
-- Definitions related to terms

-- Typing contexts (length indexed snoc-lists, isomorphic to lists).
-- Terms added to the context are well scoped in the sense that it cannot
-- contain more unbound variables than can be looked up in the context.

infixl 24 _∙_

data Con (A : Nat → Set a) : Nat → Set a where
  ε   :                             Con A 0        -- Empty context.
  _∙_ : {n : Nat} → Con A n → A n → Con A (1+ n)   -- Context extension.

private variable
  Γ : Con _ _

-- Empty-con Γ holds if Γ is empty.

data Empty-con {P : Nat → Set a} : Con P n → Set a where
  ε : Empty-con ε

-- A variant of Empty-con.

infix 4 _or-empty_

data _or-empty_ {P : Nat → Set a} (A : Set a) : Con P n → Set a where
  possibly-nonempty : ⦃ ok : A ⦄ → A or-empty Γ
  ε                 : A or-empty ε

-- Representation of sub terms using a list of binding levels

infixr 5 _∷ₜ_

data GenTs (A : Nat → Set a) : Nat → List Nat → Set a where
  []   : {n : Nat} → GenTs A n []
  _∷ₜ_ : {n b : Nat} {bs : List Nat}
         (t : A (b + n)) (ts : GenTs A n bs) → GenTs A n (b ∷ bs)

-- Sigma and Unit types have two modes, allowing either projections
-- and η-equality (strong) or elimination by prodrec/unitrec (weak).
--
-- Note that one can optionally enable η-equality for weak unit types,
-- see Definition.Typed.Variant.Type-variant.η-for-Unitʷ.
data Strength : Set where
  𝕤 𝕨 : Strength

-- Π- or Σ-types.

data BinderMode : Set where
  BMΠ : BinderMode
  BMΣ : (s : Strength) → BinderMode

-- The function drop k removes the last k entries from contexts.

drop : ∀ k → Con P (k + n) → Con P n
drop 0      Γ       = Γ
drop (1+ k) (Γ ∙ _) = drop k Γ

-- A map function for contexts.

map-Con : (∀ {n} → P n → Q n) → Con P n → Con Q n
map-Con _ ε       = ε
map-Con f (Γ ∙ A) = map-Con f Γ ∙ f A

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

stepn : {k m : Nat} (ρ : Wk k m) → (n : Nat) → Wk (n + k) m
stepn ρ 0 = ρ
stepn ρ (1+ n) = step (stepn ρ n)

-- The weakening step-at x inserts a fresh variable at position x.

step-at : Fin n → Wk n (pred n)
step-at x0                  = step id
step-at (_+1 {n = 0}    ())
step-at (_+1 {n = 1+ _} x)  = lift (step-at x)

-- A variant of step-at without lift constructors in the result.

step-at′ : (x : Fin n) → Wk (n ∸ toℕ x) (pred n ∸ toℕ x)
step-at′ x0                  = step id
step-at′ (_+1 {n = 0}    ())
step-at′ (_+1 {n = 1+ _} x)  = step-at′ x

-- Weakening of variables.
-- If η : Γ ≤ Δ and x ∈ dom(Δ) then wkVar η x ∈ dom(Γ).

wkVar : {m n : Nat} (ρ : Wk m n) (x : Fin n) → Fin m
wkVar id x            = x
wkVar (step ρ) x      = (wkVar ρ x) +1
wkVar (lift ρ) x0     = x0
wkVar (lift ρ) (x +1) = (wkVar ρ x) +1

-- A weakening for closed terms.

wk₀ : Wk n 0
wk₀ {n = 0}    = id
wk₀ {n = 1+ n} = step wk₀

------------------------------------------------------------------------
-- Universe levels

-- Universe levels.

Universe-level : Set
Universe-level = Nat

-- The maximum of two universe levels.

infixl 6 _⊔ᵘ_

_⊔ᵘ_ : (_ _ : Universe-level) → Universe-level
_⊔ᵘ_ = flip Tools.Nat._⊔_

-- The definition above is set up so that l ⊔ᵘ 0 is definitionally
-- equal to l, with the intention to make it a little easier to work
-- with Erased.

_ : l ⊔ᵘ 0 ≡ l
_ = refl

-- Ordering of universe levels.

infix 4 _≤ᵘ_

_≤ᵘ_ : (_ _ : Universe-level) → Set
i ≤ᵘ j = i ≤′ j

open Tools.Nat public
  using ()
  renaming (≤′-refl to ≤ᵘ-refl; ≤′-step to ≤ᵘ-step)

-- Strict ordering of universe levels.

infix 4 _<ᵘ_

_<ᵘ_ : (_ _ : Universe-level) → Set
i <ᵘ j = i <′ j

------------------------------------------------------------------------
-- Definition contexts

-- Unfolding vectors.
--
-- Here "1" means "unfold".

data Unfolding : Nat -> Set where
  ε  : Unfolding 0
  _⁰ : Unfolding n → Unfolding (1+ n)
  _¹ : Unfolding n → Unfolding (1+ n)

-- Merging of unfolding vectors.

infixl 5 _⊔ᵒ_

_⊔ᵒ_ : Unfolding n → Unfolding n → Unfolding n
ε    ⊔ᵒ ε     = ε
uf ⁰ ⊔ᵒ uf′ ⁰ = (uf ⊔ᵒ uf′) ⁰
uf ⁰ ⊔ᵒ uf′ ¹ = (uf ⊔ᵒ uf′) ¹
uf ¹ ⊔ᵒ uf′ ⁰ = (uf ⊔ᵒ uf′) ¹
uf ¹ ⊔ᵒ uf′ ¹ = (uf ⊔ᵒ uf′) ¹

-- A vector for unfolding everything.

ones : (n : Nat) → Unfolding n
ones 0      = ε
ones (1+ n) = ones n ¹

-- Opacity.

data Opacity (n : Nat) : Set where
  -- Opaque, with the given unfolding clause.
  opa : Unfolding n → Opacity n
  -- Transparent.
  tra : Opacity n

-- Definition contexts.

infixl 24 _∙⟨_⟩[_∷_]

data DCon (𝕋 : Set a) : Nat → Set a where
  ε          : DCon 𝕋 0
  _∙⟨_⟩[_∷_] : DCon 𝕋 n → Opacity n → 𝕋 → 𝕋 → DCon 𝕋 (1+ n)

private variable
  ∇ : DCon _ _
  ω : Opacity _
  φ : Unfolding _

-- The type α ↦∷ A ∈ ∇ means that α has type A in ∇.

data _↦∷_∈_ {𝕋 : Set a} : Nat → 𝕋 → DCon 𝕋 n → Set a where
  here  : ∀ {A t} {∇ : DCon 𝕋 n} → n ↦∷ A ∈ ∇ ∙⟨ ω ⟩[ t ∷ A ]
  there : ∀ {A B u} → α ↦∷ A ∈ ∇ → α ↦∷ A ∈ ∇ ∙⟨ ω ⟩[ u ∷ B ]

-- The type α ↦ t ∷ A ∈ ∇ means that α is (transparently) equal to t
-- of type A in ∇.

data _↦_∷_∈_ {𝕋 : Set a} : Nat → 𝕋 → 𝕋 → DCon 𝕋 n → Set a where
  here  : ∀ {A t} {∇ : DCon 𝕋 n}      → n ↦ t ∷ A ∈ ∇ ∙⟨ tra ⟩[ t ∷ A ]
  there : ∀ {A B t u} → α ↦ t ∷ A ∈ ∇ → α ↦ t ∷ A ∈ ∇ ∙⟨ ω   ⟩[ u ∷ B ]

-- The type α ↦⊘∷ A ∈ ∇ means that α is an opaque definition of type A
-- in ∇.

data _↦⊘∷_∈_ {𝕋 : Set a} : Nat → 𝕋 → DCon 𝕋 n → Set a where
  here  : ∀ {A t} {∇ : DCon 𝕋 n}  → n ↦⊘∷ A ∈ ∇ ∙⟨ opa φ ⟩[ t ∷ A ]
  there : ∀ {A B u} → α ↦⊘∷ A ∈ ∇ → α ↦⊘∷ A ∈ ∇ ∙⟨ ω     ⟩[ u ∷ B ]

-- Glassification.

glassify : {𝕋 : Set a} → DCon 𝕋 n → DCon 𝕋 n
glassify ε                       = ε
glassify (∇ ∙⟨ ω ⟩[ t ∷ A ]) = glassify ∇ ∙⟨ tra ⟩[ t ∷ A ]

-- A definition context is transparent if it is equal to its own
-- "glassification".

Transparent : {𝕋 : Set a} → DCon 𝕋 n → Set a
Transparent ∇ = ∇ ≡ glassify ∇

-- Definition context extensions.

data DExt (𝕋 : Set a) : Nat → Nat → Set a where
  id   : n ≡ m → DExt 𝕋 m n
  step : DExt 𝕋 m n → Opacity m → 𝕋 → 𝕋 → DExt 𝕋 (1+ m) n

pattern idᵉ         = id refl
pattern step₁ ω A t = step idᵉ ω A t

-- Concatenation of definition context extensions.

_•ᵈ_ : {𝕋 : Set a} → DExt 𝕋 m n → DExt 𝕋 n l → DExt 𝕋 m l
id eq         •ᵈ ξ = subst (flip (DExt _) _) eq ξ
step ξ′ ω A t •ᵈ ξ = step (ξ′ •ᵈ ξ) ω A t

-- A map function for definition contexts.

map-DCon : (𝕋 → 𝕌) → DCon 𝕋 n → DCon 𝕌 n
map-DCon _ ε                   = ε
map-DCon f (∇ ∙⟨ ω ⟩[ t ∷ A ]) =
  map-DCon f ∇ ∙⟨ ω ⟩[ f t ∷ f A ]

------------------------------------------------------------------------
-- Context pairs

-- Pairs of definition contexts and variable contexts.

infix 5 _»_

record Context-pair (P : Nat → Set a) (m n : Nat) : Set a where
  constructor _»_
  field
    -- The definition context.
    defs : DCon (P 0) m
    -- The variable context.
    vars : Con P n

open Context-pair public

-- A variant of Con._∙_ for Context-pair.

infixl 24 _»∙_

_»∙_ : Context-pair P m n → P n → Context-pair P m (1+ n)
(∇ » Γ) »∙ A = ∇ » Γ ∙ A

-- A map function for context pairs.

map-Cons : (∀ {n} → P n → Q n) → Context-pair P m n → Context-pair Q m n
map-Cons f (∇ » Γ) = map-DCon f ∇ » map-Con f Γ
