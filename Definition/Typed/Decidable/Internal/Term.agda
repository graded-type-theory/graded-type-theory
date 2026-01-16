------------------------------------------------------------------------
-- Terms used by Definition.Typed.Decidable.Internal, along with
-- translation to regular terms
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Decidable.Internal.Term
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.Untyped M as U
  using (BinderMode; Opacity; Strength; Unfolding; Wk; _»_)
open import Definition.Untyped.Properties M
import Definition.Untyped.Sup R as S

open U.Con
open U.DCon

import Graded.Mode 𝕄 as Mode

open import Tools.Bool using (Bool; T)
open import Tools.Empty
open import Tools.Function
open import Tools.Fin
open import Tools.List as L using (List)
open import Tools.Maybe
open import Tools.Nat as N using (Nat; 1+; 2+)
open import Tools.Product
open import Tools.PropositionalEquality hiding (subst)
open import Tools.Relation
open import Tools.Vec as Vec using (Vec)

private
  module M = Modality 𝕄

private variable
  b                     : Bool
  m n n₁ n₂ n₃ n₄ n₅ n₆ : Nat
  x                     : Fin _

------------------------------------------------------------------------
-- Terms for grades, universe levels, strengths and binder modes

-- Grade terms.

infixr 40 _+_
infixr 43 _∧_
infixr 45 _·_

data Termᵍ (n : Nat) : Set a where
  var         : (x : Fin n) → Termᵍ n
  𝟘 𝟙 ω       : Termᵍ n
  _+_ _·_ _∧_ : (p q : Termᵍ n) → Termᵍ n
  ⌜⌞_⌟⌝       : (p : Termᵍ n) → Termᵍ n

-- Strength terms.

data Termˢ (n : Nat) : Set where
  var : (x : Fin n) → Termˢ n
  𝕤 𝕨 : Termˢ n

-- Binder mode terms.

data Termᵇᵐ (m n : Nat) : Set where
  var : (x : Fin n) → Termᵇᵐ m n
  BMΠ : Termᵇᵐ m n
  BMΣ : (s : Termˢ m) → Termᵇᵐ m n

------------------------------------------------------------------------
-- Terms

-- "Constant" parameters for the term type.

record Constants : Set where
  field
    -- The number of grade variables.
    gs : Nat

    -- The number of strength variables.
    ss : Nat

    -- The number of binder mode variables.
    bms : Nat

    -- The number of meta-variables.
    ms : Nat

    -- The lengths of the contexts for each of the meta-variables.
    meta-con-size : Vec Nat ms

    -- The length of the base definition context (see below).
    base-dcon-size : Nat

    -- Is the base variable context allowed?
    base-con-allowed : Bool

    -- The length of the base variable context (see below), if any.
    base-con-size : Nat

  -- Is the base variable context allowed?

  Base-con-allowed : Set
  Base-con-allowed = T base-con-allowed

open Constants public

private variable
  c : Constants

mutual

  -- Terms:
  --
  -- * Regular term constructors. These take grade terms, universe
  --   level terms, etc., so that one can check equality of, say,
  --   grades that are meta-level variables. (The equality check for
  --   grades is at the time of writing only a syntactic check, the
  --   modality laws have not been implemented.)
  --
  -- * One can optionally annotate some term constructors with extra
  --   information. This feature is included so that one can have
  --   things like β-redexes in the terms to be type-checked.
  --
  -- * Variables ("meta-variables") that refer to regular terms or
  --   types. This feature is included so that one can refer to
  --   something that is a meta-level variable. It is possible to
  --   check if two meta-variables are equal. In the presence of a
  --   meta-variable context one can also check if a meta-variable
  --   stands for a well-formed type or a well-typed term, and in the
  --   latter case the term's type can be obtained.
  --
  -- * Explicit weakenings and substitutions. These terms are
  --   translated to regular terms using the function ⌜_⌝ defined
  --   below, and the inclusion of term constructors for applying
  --   weakenings or substitutions ensures that no proof is needed to
  --   show that, say, the translation of the term
  --   subst (var x0) (sgSubst (var x1)) is the regular term
  --   var x0 [ var x1 ]₀: the translation "automatically" has the
  --   right form.

  infix  30 ΠΣ⟨_⟩_,_▷_▹_
  infixr 30 _supᵘₗ_
  infixl 30 _∘⟨_⟩_

  data Term (c : Constants) (n : Nat) : Set a where
    meta-var     : (x : Meta-var c m) (σ : Subst c n m) → Term c n
    weaken       : (ρ : Wk n m) (t : Term c m) → Term c n
    subst        : (t : Term c m) (σ : Subst c n m) → Term c n
    var          : (x : Fin n) → Term c n
    defn         : (α : Nat) → Term c n
    Level        : Term c n
    zeroᵘ        : Term c n
    sucᵘ         : (l : Term c n) → Term c n
    _supᵘₗ_      : (l₁ l₂ : Term c n) → Term c n
    U            : (l : Term c n) → Term c n
    Lift         : (l A : Term c n) → Term c n
    lift         : (l : Maybe (Term c n)) (t : Term c n) → Term c n
    lower        : (t : Term c n) → Term c n
    Empty        : Term c n
    emptyrec     : (p : Termᵍ (c .gs)) (A t : Term c n) → Term c n
    Unit         : (s : Termˢ (c .ss)) → Term c n
    star         : (s : Termˢ (c .ss)) → Term c n
    unitrec      : (p q : Termᵍ (c .gs)) (A : Term c (1+ n))
                   (t u : Term c n) → Term c n
    ΠΣ⟨_⟩_,_▷_▹_ : (b : Termᵇᵐ (c .ss) (c .bms)) (p q : Termᵍ (c .gs))
                   (A : Term c n) (B : Term c (1+ n)) → Term c n
    lam          : (p : Termᵍ (c .gs))
                   (qA : Maybe (Termᵍ (c .gs) × Term c n))
                   (t : Term c (1+ n)) → Term c n
    _∘⟨_⟩_       : (t : Term c n) (p : Termᵍ (c .gs)) (u : Term c n) →
                   Term c n
    prod         : (s : Termˢ (c .ss)) (p : Termᵍ (c .gs))
                   (qB : Maybe (Termᵍ (c .gs) × Term c (1+ n)))
                   (t u : Term c n) → Term c n
    fst          : (p : Termᵍ (c .gs)) (t : Term c n) → Term c n
    snd          : (p : Termᵍ (c .gs)) (t : Term c n) → Term c n
    prodrec      : (r p q : Termᵍ (c .gs)) (A : Term c (1+ n))
                   (t : Term c n) (u : Term c (2+ n)) → Term c n
    ℕ            : Term c n
    zero         : Term c n
    suc          : (t : Term c n) → Term c n
    natrec       : (p q r : Termᵍ (c .gs)) (A : Term c (1+ n))
                   (t : Term c n) (u : Term c (2+ n)) (v : Term c n) →
                   Term c n
    Id           : (A t u : Term c n) → Term c n
    rfl          : (t : Maybe (Term c n)) → Term c n
    J            : (p q : Termᵍ (c .gs)) (A t : Term c n)
                   (B : Term c (2+ n)) (u v w : Term c n) → Term c n
    K            : (p : Termᵍ (c .gs)) (A t : Term c n)
                   (B : Term c (1+ n)) (u v : Term c n) → Term c n
    []-cong      : (s : Termˢ (c .ss)) (l A t u v : Term c n) → Term c n

  -- Substitutions.
  --
  -- This representation of substitutions is used to make it possible
  -- to, at least sometimes, compare substitutions even if the
  -- contexts' lengths are unknown (meta-level variables).

  infix 35 _⇑

  data Subst (c : Constants) : Nat → Nat → Set a where
    id   : Subst c n n
    wk1  : Subst c n₂ n₁ → Subst c (1+ n₂) n₁
    _⇑   : Subst c n₂ n₁ → Subst c (1+ n₂) (1+ n₁)
    cons : Subst c n₂ n₁ → Term c n₂ → Subst c n₂ (1+ n₁)

  -- The type Meta-var c n represents meta-variables.

  data Meta-var (c : Constants) (n : Nat) : Set where
    var : (x : Fin (c .ms)) → Vec.lookup (c .meta-con-size) x ≡ n →
          Meta-var c n

pattern var! x = var x refl

------------------------------------------------------------------------
-- Constraints

-- Constraints that can be imposed by the type-checker and other
-- procedures.

data Constraint (c : Constants) : Set a where
  k-allowed level-allowed level-is-small no-equality-reflection
    opacity-allowed unfolding-mode-transitive :
    Constraint c
  box-cong-allowed unit-allowed unit-with-η :
    (s : Termˢ (c .ss)) → Constraint c
  πσ-allowed :
    (b : Termᵇᵐ (c .ss) (c .bms)) (p q : Termᵍ (c .gs)) → Constraint c

pattern π-allowed p q   = πσ-allowed BMΠ p q
pattern σ-allowed s p q = πσ-allowed (BMΣ s) p q
pattern σˢ-allowed p q  = σ-allowed 𝕤 p q
pattern σʷ-allowed p q  = σ-allowed 𝕨 p q

------------------------------------------------------------------------
-- Contexts

-- Definition contexts.
--
-- The constructor base stands for a dedicated "base" definition
-- context (with an optional suspended unfolding). The idea is that it
-- should be possible to let this refer to a meta-level variable. One
-- could imagine having context variables, but perhaps there would be
-- little need for that.

infixl 24 _∙⟨_⟩[_∷_]

data DCon (c : Constants) : Nat → Set a where
  base       : Maybe (Unfolding (c .base-dcon-size)) →
               DCon c (c .base-dcon-size)
  ε          : DCon c 0
  _∙⟨_⟩[_∷_] : DCon c n → Opacity n → Term c 0 → Term c 0 →
               DCon c (1+ n)

-- Variable contexts.
--
-- The constructor base stands for a dedicated "base" variable
-- context. The idea is that it should be possible to let this refer
-- to a meta-level variable. One could imagine having context
-- variables, but perhaps there would be little need for that.

infixl 24 _∙_

data Con (c : Constants) : Nat → Set a where
  base : {b : Base-con-allowed c} → Con c (c .base-con-size)
  ε    : Con c 0
  _∙_  : Con c n → Term c n → Con c (1+ n)

-- Types, terms with types, or levels.

data Type-or-term (c : Constants) (n : Nat) : Set a where
  type  : (A : U.Term n) → Type-or-term c n
  term  : (t : U.Term n) (A : Term c n) → Type-or-term c n
  level : (l : U.Term n) → Type-or-term c n

-- Meta-variable contexts.
--
-- Meta-variables can refer to types, terms and levels in possibly
-- different variable contexts. The idea is that it should be possible
-- to work relative to terms, types and levels that are well-formed
-- with respect to variable contexts that are extensions of some base
-- context.
--
-- Different meta-variables can also refer to definitionally equal
-- terms, types or levels.

record Meta-con (c : Constants) : Set a where
  no-eta-equality
  field
    bindings :
      ∀ {n} (x : Meta-var c n) →
      Con c n × Type-or-term c n
    equalities :
      List (∃ λ n → Meta-var c n × Meta-var c n)

open Meta-con public

-- If the number of meta-variables is zero, then there are no
-- meta-variables.

¬-Meta-var : c .ms ≡ 0 → ¬ Meta-var c n
¬-Meta-var refl (var () _)

-- An empty meta-variable context.

emptyᶜᵐ :
  Meta-con
    (record
       { gs               = n₁
       ; ss               = n₃
       ; bms              = n₄
       ; ms               = 0
       ; meta-con-size    = Vec.[]
       ; base-dcon-size   = n₅
       ; base-con-allowed = b
       ; base-con-size    = n₆
       })
emptyᶜᵐ .bindings   = ⊥-elim ∘→ ¬-Meta-var refl
emptyᶜᵐ .equalities = L.[]

-- A grade context, a universe level context, a strength context, a
-- binder mode context, a list of constraints, a meta-variable
-- context, and a base context.

record Contexts (c : Constants) : Set a where
  no-eta-equality
  field
    grades       : Vec M (c .gs)
    strengths    : Vec Strength (c .ss)
    binder-modes : Vec BinderMode (c .bms)
    constraints  : List (Constraint c)
    metas        : Meta-con c
    ⌜base⌝       : U.Cons (c .base-dcon-size) (c .base-con-size)

open Contexts public

private variable
  γ : Contexts _

-- Empty contexts.

empty-Contexts :
  (b : Bool) →
  Contexts
    (record
       { gs               = 0
       ; ss               = 0
       ; bms              = 0
       ; ms               = 0
       ; meta-con-size    = Vec.[]
       ; base-dcon-size   = 0
       ; base-con-allowed = b
       ; base-con-size    = 0
       })
empty-Contexts _ .grades       = Vec.[]
empty-Contexts _ .strengths    = Vec.[]
empty-Contexts _ .binder-modes = Vec.[]
empty-Contexts _ .constraints  = List.[]
empty-Contexts _ .metas        = emptyᶜᵐ
empty-Contexts _ .⌜base⌝       = ε » ε

-- Context pairs.

infix 5 _»_

record Cons (c : Constants) (m n : Nat) : Set a where
  constructor _»_
  field
    -- The definition context.
    defs : DCon c m

    -- The variable context.
    vars : Con c n

open Cons public

-- An empty context pair.

emptyᶜ : Cons c 0 0
emptyᶜ = record { defs = ε; vars = ε }

-- A variant of _∙_ for Cons.

infixl 24 _»∙_

_»∙_ : Cons c m n → Term c n → Cons c m (1+ n)
Γ »∙ A = Γ .defs » Γ .vars ∙ A

------------------------------------------------------------------------
-- A simple test

-- The substitution is equal to id.

data Is-id {c : Constants} {n₁} : Subst c n₂ n₁ → Set a where
  id : Is-id id

-- Is the substitution equal to id?

is-id? : (σ : Subst c n₂ n₁) → Maybe (Is-id σ)
is-id? id = just id
is-id? _  = nothing

------------------------------------------------------------------------
-- Translation

-- Translates grade terms to grades.

⟦_⟧ᵍ : Termᵍ (c .gs) → Contexts c → M
⟦ var x   ⟧ᵍ γ = Vec.lookup (γ .grades) x
⟦ 𝟘       ⟧ᵍ γ = M.𝟘
⟦ 𝟙       ⟧ᵍ γ = M.𝟙
⟦ ω       ⟧ᵍ γ = M.ω
⟦ t₁ + t₂ ⟧ᵍ γ = ⟦ t₁ ⟧ᵍ γ M.+ ⟦ t₂ ⟧ᵍ γ
⟦ t₁ · t₂ ⟧ᵍ γ = ⟦ t₁ ⟧ᵍ γ M.· ⟦ t₂ ⟧ᵍ γ
⟦ t₁ ∧ t₂ ⟧ᵍ γ = ⟦ t₁ ⟧ᵍ γ M.∧ ⟦ t₂ ⟧ᵍ γ
⟦ ⌜⌞ t ⌟⌝ ⟧ᵍ γ = Mode.⌜ Mode.⌞ ⟦ t ⟧ᵍ γ ⌟ ⌝

-- Translates strength terms to strengths.

⟦_⟧ˢ : Termˢ (c .ss) → Contexts c → Strength
⟦ var x ⟧ˢ γ = Vec.lookup (γ .strengths) x
⟦ 𝕤     ⟧ˢ _ = U.𝕤
⟦ 𝕨     ⟧ˢ _ = U.𝕨

-- Translates binder mode terms to binder modes.

⟦_⟧ᵇᵐ : Termᵇᵐ (c .ss) (c .bms) → Contexts c → BinderMode
⟦ var x ⟧ᵇᵐ γ = Vec.lookup (γ .binder-modes) x
⟦ BMΠ   ⟧ᵇᵐ _ = U.BMΠ
⟦ BMΣ s ⟧ᵇᵐ γ = U.BMΣ (⟦ s ⟧ˢ γ)

mutual

  -- Turns terms into regular terms.

  ⌜_⌝ : Term c n → Contexts c → U.Term n
  ⌜ meta-var x σ ⌝ γ with is-id? σ
  … | just id = ⌜ x ⌝ᵐ γ
  … | nothing = ⌜ x ⌝ᵐ γ U.[ ⌜ σ ⌝ˢ γ ]
  ⌜ weaken ρ t              ⌝ γ = U.wk ρ (⌜ t ⌝ γ)
  ⌜ subst t σ               ⌝ γ = ⌜ t ⌝ γ U.[ ⌜ σ ⌝ˢ γ ]
  ⌜ var x                   ⌝ _ = U.var x
  ⌜ defn α                  ⌝ _ = U.defn α
  ⌜ Level                   ⌝ _ = U.Level
  ⌜ zeroᵘ                   ⌝ _ = U.zeroᵘ
  ⌜ sucᵘ l                  ⌝ γ = U.sucᵘ (⌜ l ⌝ γ)
  ⌜ l₁ supᵘₗ l₂             ⌝ γ = ⌜ l₁ ⌝ γ S.supᵘₗ ⌜ l₂ ⌝ γ
  ⌜ Lift l A                ⌝ γ = U.Lift (⌜ l ⌝ γ) (⌜ A ⌝ γ)
  ⌜ lift _ t                ⌝ γ = U.lift (⌜ t ⌝ γ)
  ⌜ lower t                 ⌝ γ = U.lower (⌜ t ⌝ γ)
  ⌜ U l                     ⌝ γ = U.U (⌜ l ⌝ γ)
  ⌜ Empty                   ⌝ _ = U.Empty
  ⌜ emptyrec p A t          ⌝ γ = U.emptyrec (⟦ p ⟧ᵍ γ) (⌜ A ⌝ γ)
                                    (⌜ t ⌝ γ)
  ⌜ Unit s                  ⌝ γ = U.Unit (⟦ s ⟧ˢ γ)
  ⌜ star s                  ⌝ γ = U.star (⟦ s ⟧ˢ γ)
  ⌜ unitrec p q A t₁ t₂     ⌝ γ = U.unitrec (⟦ p ⟧ᵍ γ) (⟦ q ⟧ᵍ γ)
                                    (⌜ A ⌝ γ) (⌜ t₁ ⌝ γ) (⌜ t₂ ⌝ γ)
  ⌜ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ A₂ ⌝ γ = U.ΠΣ⟨ ⟦ b ⟧ᵇᵐ γ ⟩ ⟦ p ⟧ᵍ γ ,
                                    ⟦ q ⟧ᵍ γ ▷ ⌜ A₁ ⌝ γ ▹ ⌜ A₂ ⌝ γ
  ⌜ lam p _ t               ⌝ γ = U.lam (⟦ p ⟧ᵍ γ) (⌜ t ⌝ γ)
  ⌜ t₁ ∘⟨ p ⟩ t₂            ⌝ γ = ⌜ t₁ ⌝ γ U.∘⟨ ⟦ p ⟧ᵍ γ ⟩ ⌜ t₂ ⌝ γ
  ⌜ prod s p _ t₁ t₂        ⌝ γ = U.prod (⟦ s ⟧ˢ γ) (⟦ p ⟧ᵍ γ)
                                    (⌜ t₁ ⌝ γ) (⌜ t₂ ⌝ γ)
  ⌜ fst p t                 ⌝ γ = U.fst (⟦ p ⟧ᵍ γ) (⌜ t ⌝ γ)
  ⌜ snd p t                 ⌝ γ = U.snd (⟦ p ⟧ᵍ γ) (⌜ t ⌝ γ)
  ⌜ prodrec r p q A t₁ t₂   ⌝ γ = U.prodrec (⟦ r ⟧ᵍ γ) (⟦ p ⟧ᵍ γ)
                                    (⟦ q ⟧ᵍ γ) (⌜ A ⌝ γ) (⌜ t₁ ⌝ γ)
                                    (⌜ t₂ ⌝ γ)
  ⌜ ℕ                       ⌝ _ = U.ℕ
  ⌜ zero                    ⌝ _ = U.zero
  ⌜ suc t                   ⌝ γ = U.suc (⌜ t ⌝ γ)
  ⌜ natrec p q r A t₁ t₂ t₃ ⌝ γ = U.natrec (⟦ p ⟧ᵍ γ) (⟦ q ⟧ᵍ γ)
                                    (⟦ r ⟧ᵍ γ) (⌜ A ⌝ γ) (⌜ t₁ ⌝ γ)
                                    (⌜ t₂ ⌝ γ) (⌜ t₃ ⌝ γ)
  ⌜ Id A t₁ t₂              ⌝ γ = U.Id (⌜ A ⌝ γ) (⌜ t₁ ⌝ γ) (⌜ t₂ ⌝ γ)
  ⌜ rfl _                   ⌝ _ = U.rfl
  ⌜ J p q A₁ t₁ A₂ t₂ t₃ t₄ ⌝ γ = U.J (⟦ p ⟧ᵍ γ) (⟦ q ⟧ᵍ γ) (⌜ A₁ ⌝ γ)
                                    (⌜ t₁ ⌝ γ) (⌜ A₂ ⌝ γ) (⌜ t₂ ⌝ γ)
                                    (⌜ t₃ ⌝ γ) (⌜ t₄ ⌝ γ)
  ⌜ K p A₁ t₁ A₂ t₂ t₃      ⌝ γ = U.K (⟦ p ⟧ᵍ γ) (⌜ A₁ ⌝ γ) (⌜ t₁ ⌝ γ)
                                    (⌜ A₂ ⌝ γ) (⌜ t₂ ⌝ γ) (⌜ t₃ ⌝ γ)
  ⌜ []-cong s l A t₁ t₂ t₃  ⌝ γ = U.[]-cong (⟦ s ⟧ˢ γ) (⌜ l ⌝ γ)
                                    (⌜ A ⌝ γ) (⌜ t₁ ⌝ γ) (⌜ t₂ ⌝ γ)
                                    (⌜ t₃ ⌝ γ)

  -- Turns substitutions into regular substitutions.

  ⌜_⌝ˢ : Subst c n₂ n₁ → Contexts c → U.Subst n₂ n₁
  ⌜ id       ⌝ˢ γ = U.idSubst
  ⌜ wk1 σ    ⌝ˢ γ = U.wk1Subst (⌜ σ ⌝ˢ γ)
  ⌜ σ ⇑      ⌝ˢ γ = ⌜ σ ⌝ˢ γ U.⇑
  ⌜ cons σ t ⌝ˢ γ = U.consSubst (⌜ σ ⌝ˢ γ) (⌜ t ⌝ γ)

  -- Turns meta-variables into regular terms.

  ⌜_⌝ᵐ : Meta-var c n → Contexts c → U.Term n
  ⌜ x ⌝ᵐ γ with γ .metas .bindings x
  … | _ , type A   = A
  … | _ , term t _ = t
  … | _ , level l  = l

opaque

  -- The definition of ⌜_⌝ for meta-var includes a special case for
  -- id, intended to make the type-checker a little easier to use.
  -- That special case does not affect the function's result.

  ⌜meta-var⌝ :
    {x : Meta-var c n₁} (σ : Subst c n₂ n₁) →
    ⌜ meta-var x σ ⌝ γ ≡ ⌜ x ⌝ᵐ γ U.[ ⌜ σ ⌝ˢ γ ]
  ⌜meta-var⌝ σ with is-id? σ
  … | just id = sym (subst-id _)
  … | nothing = refl

------------------------------------------------------------------------
-- An abbreviation

-- A variant of the constructor meta-var.

varᵐ : (x : Fin (c .ms)) → Term c (Vec.lookup (c .meta-con-size) x)
varᵐ x = meta-var (var! x) id

opaque

  -- The function varᵐ is correctly implemented.

  ⌜varᵐ⌝ :
    (γ : Contexts c) →
    ⌜ varᵐ x ⌝ γ ≡ ⌜ var x refl ⌝ᵐ γ
  ⌜varᵐ⌝ _ = refl

------------------------------------------------------------------------
-- Some abbreviations

-- Π-types.

infix 30 Π_,_▷_▹_

Π_,_▷_▹_ : (p q : Termᵍ (c .gs)) → Term c n → Term c (1+ n) → Term c n
Π p , q ▷ A ▹ B = ΠΣ⟨ BMΠ ⟩ p , q ▷ A ▹ B

-- Strong Σ-types.

infix 30 Σˢ_,_▷_▹_

Σˢ_,_▷_▹_ : (p q : Termᵍ (c .gs)) → Term c n → Term c (1+ n) → Term c n
Σˢ p , q ▷ A ▹ B = ΠΣ⟨ BMΣ 𝕤 ⟩ p , q ▷ A ▹ B

-- Weak Σ-types.

infix 30 Σʷ_,_▷_▹_

Σʷ_,_▷_▹_ : (p q : Termᵍ (c .gs)) → Term c n → Term c (1+ n) → Term c n
Σʷ p , q ▷ A ▹ B = ΠΣ⟨ BMΣ 𝕨 ⟩ p , q ▷ A ▹ B

-- The type constructor Erased.

Erased : Termˢ (c .ss) → (_ _ : Term c n) → Term c n
Erased s l A =
  ΠΣ⟨ BMΣ s ⟩ 𝟘 , 𝟘 ▷ A ▹ Lift (weaken (U.step U.id) l) (Unit s)

-- The term constructor [_].

box : Termˢ (c .ss) → (_ _ : Term c n) → Term c n
box s l t =
  prod s 𝟘 (just (𝟘 , Lift (weaken (U.step U.id) l) (Unit s))) t
    (lift (just l) (star s))
