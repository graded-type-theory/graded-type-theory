------------------------------------------------------------------------
-- Terms used by Definition.Typed.Decidable.Internal, along with
-- translation to regular terms
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality
open import Graded.Usage.Restrictions

module Definition.Typed.Decidable.Internal.Term
  {a} {M : Set a}
  {𝕄 : Modality M}
  (TR : Type-restrictions 𝕄)
  (UR : Usage-restrictions 𝕄)
  where

open Usage-restrictions UR

open import Definition.Typed TR

open import Definition.Untyped M as U
  using
    (BinderMode; Opacity; Strength; Unfolding; Universe-level; Wk; _»_)
open import Definition.Untyped.Properties M

open U.Con
open U.DCon
open Opacity

open import Graded.Usage.Restrictions.Natrec 𝕄

open import Tools.Bool using (Bool; T)
open import Tools.Fin
open import Tools.Maybe
open import Tools.Nat as N using (Nat; 1+; 2+)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Vec as Vec using (Vec)

private
  module M = Modality 𝕄

private variable
  b                        : Bool
  m n n′ n₁ n₂ n₃ n₄ n₅ n₆ : Nat
  x                        : Fin _

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
  nr          : ⦃ has-nr : Nr-available ⦄
                (p₁ p₂ p₃ p₄ p₅ : Termᵍ n) → Termᵍ n

-- Universe level terms.

data Termˡ (n : Nat) : Set where
  var  : (x : Fin n) → Termˡ n
  zero : Termˡ n
  suc  : (l : Termˡ n) → Termˡ n
  _⊔ᵘ_ : (l₁ l₂ : Termˡ n) → Termˡ n

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

    -- The number of universe level variables.
    ls : Nat

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
  -- * Type annotations. This feature is included so that one can, at
  --   least sometimes, have things like β-redexes in the terms to be
  --   type-checked. Note that type annotations are not preserved by
  --   reduction, and might be ignored by the type-checker.
  --
  -- * Variables ("meta-variables") that refer to regular terms or
  --   types. This feature is included so that one can refer to
  --   something that is a meta-level variable. It is possible to
  --   check if two meta-variables are equal. In the presence of a
  --   meta-variable context one can also check if a meta-variable
  --   stands for a well-formed type or a well-typed term, and in the
  --   latter case the term's type can be obtained.
  --
  -- * Embedded regular terms (combined with substitutions). Note that
  --   the type-checker does not support these terms. TODO: Remove
  --   support for them.
  --
  -- * Explicit weakenings and substitutions. These terms are
  --   translated to regular terms using the function ⌜_⌝ defined
  --   below, and the inclusion of term constructors for applying
  --   weakenings or substitutions ensures that no proof is needed to
  --   show that, say, the translation of the term
  --   subst (var x0) (sgSubst (var x1)) is the regular term
  --   var x0 [ var x1 ]₀: the translation "automatically" has the
  --   right form.

  infixl 35 _∷[_]
  infix  30 ΠΣ⟨_⟩_,_▷_▹_
  infixl 30 _∘⟨_⟩_

  data Term (c : Constants) (n : Nat) : Set a where
    _∷[_]        : (t A : Term c n) → Term c n
    meta-var     : (x : Meta-var c m) (σ : Subst c n m) → Term c n
    ⌞_⌟          : (t : U.Term m) (σ : Subst c n m) → Term c n
    weaken       : (ρ : Wk n m) (t : Term c m) → Term c n
    subst        : (t : Term c m) (σ : Subst c n m) → Term c n
    var          : (x : Fin n) → Term c n
    defn         : (α : Nat) → Term c n
    U            : (l : Termˡ (c .ls)) → Term c n
    Empty        : Term c n
    emptyrec     : (p : Termᵍ (c .gs)) (A t : Term c n) → Term c n
    Unit         : (s : Termˢ (c .ss)) (l : Termˡ (c .ls)) → Term c n
    star         : (s : Termˢ (c .ss)) (l : Termˡ (c .ls)) → Term c n
    unitrec      : (l : Termˡ (c .ls)) (p q : Termᵍ (c .gs))
                   (A : Term c (1+ n)) (t u : Term c n) → Term c n
    ΠΣ⟨_⟩_,_▷_▹_ : (b : Termᵇᵐ (c .ss) (c .bms)) (p q : Termᵍ (c .gs))
                   (A : Term c n) (B : Term c (1+ n)) → Term c n
    lam          : (p : Termᵍ (c .gs)) (t : Term c (1+ n)) → Term c n
    _∘⟨_⟩_       : (t : Term c n) (p : Termᵍ (c .gs)) (u : Term c n) →
                   Term c n
    prod         : (s : Termˢ (c .ss)) (p : Termᵍ (c .gs))
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
    rfl          : Term c n
    J            : (p q : Termᵍ (c .gs)) (A t : Term c n)
                   (B : Term c (2+ n)) (u v w : Term c n) → Term c n
    K            : (p : Termᵍ (c .gs)) (A t : Term c n)
                   (B : Term c (1+ n)) (u v : Term c n) → Term c n
    []-cong      : (s : Termˢ (c .ss)) (A t u v : Term c n) → Term c n

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
    var : (x : Fin (c .ms)) → Vec.lookup (c .meta-con-size) x PE.≡ n →
          Meta-var c n

pattern var! x = var x PE.refl

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

-- Types or terms with types.

data Type-or-term (c : Constants) (n : Nat) : Set a where
  type : (A : U.Term n) → Type-or-term c n
  term : (t : U.Term n) (A : Term c n) → Type-or-term c n

-- Meta-variable contexts.
--
-- Meta-variables can refer to types and terms in possibly different
-- variable contexts. The idea is that it should be possible to work
-- relative to terms and types that are well-formed with respect to
-- variable contexts that are extensions of some base context.

record Meta-con (c : Constants) : Set a where
  no-eta-equality
  field
    bindings :
      ∀ {n} (x : Meta-var c n) →
      Con c n × Type-or-term c n

open Meta-con public

-- An empty meta-variable context.

emptyᶜᵐ :
  Meta-con
    (record
       { gs               = n₁
       ; ls               = n₂
       ; ss               = n₃
       ; bms              = n₄
       ; ms               = 0
       ; meta-con-size    = Vec.[]
       ; base-dcon-size   = n₅
       ; base-con-allowed = b
       ; base-con-size    = n₆
       })
emptyᶜᵐ .bindings (var () _)

-- A grade context, a universe level context, a strength context, a
-- binder mode context, a meta-variable context, and a base context.

record Contexts (c : Constants) : Set a where
  no-eta-equality
  field
    grades       : Vec M (c .gs)
    levels       : Vec Universe-level (c .ls)
    strengths    : Vec Strength (c .ss)
    binder-modes : Vec BinderMode (c .bms)
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
       ; ls               = 0
       ; ss               = 0
       ; bms              = 0
       ; ms               = 0
       ; meta-con-size    = Vec.[]
       ; base-dcon-size   = 0
       ; base-con-allowed = b
       ; base-con-size    = 0
       })
empty-Contexts _ .grades       = Vec.[]
empty-Contexts _ .levels       = Vec.[]
empty-Contexts _ .strengths    = Vec.[]
empty-Contexts _ .binder-modes = Vec.[]
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
⟦ var x                        ⟧ᵍ γ = Vec.lookup (γ .grades) x
⟦ 𝟘                            ⟧ᵍ γ = M.𝟘
⟦ 𝟙                            ⟧ᵍ γ = M.𝟙
⟦ ω                            ⟧ᵍ γ = M.ω
⟦ t₁ + t₂                      ⟧ᵍ γ = ⟦ t₁ ⟧ᵍ γ M.+ ⟦ t₂ ⟧ᵍ γ
⟦ t₁ · t₂                      ⟧ᵍ γ = ⟦ t₁ ⟧ᵍ γ M.· ⟦ t₂ ⟧ᵍ γ
⟦ t₁ ∧ t₂                      ⟧ᵍ γ = ⟦ t₁ ⟧ᵍ γ M.∧ ⟦ t₂ ⟧ᵍ γ
⟦ nr ⦃ has-nr ⦄ t₁ t₂ t₃ t₄ t₅ ⟧ᵍ γ =
  Has-nr.nr (Natrec-mode-Has-nr has-nr)
    (⟦ t₁ ⟧ᵍ γ) (⟦ t₂ ⟧ᵍ γ) (⟦ t₃ ⟧ᵍ γ) (⟦ t₄ ⟧ᵍ γ) (⟦ t₅ ⟧ᵍ γ)

-- Translates universe level terms to universe levels.

⟦_⟧ˡ : Termˡ (c .ls) → Contexts c → Universe-level
⟦ var x    ⟧ˡ γ = Vec.lookup (γ .levels) x
⟦ zero     ⟧ˡ _ = 0
⟦ suc l    ⟧ˡ γ = 1+ (⟦ l ⟧ˡ γ)
⟦ l₁ ⊔ᵘ l₂ ⟧ˡ γ = ⟦ l₁ ⟧ˡ γ U.⊔ᵘ ⟦ l₂ ⟧ˡ γ

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
  ⌜ t ∷[ _ ]     ⌝ γ = ⌜ t ⌝ γ
  ⌜ meta-var x σ ⌝ γ with is-id? σ
  … | just id = ⌜ x ⌝ᵐ γ
  … | nothing = ⌜ x ⌝ᵐ γ U.[ ⌜ σ ⌝ˢ γ ]
  ⌜ ⌞ t ⌟ σ                 ⌝ γ = t U.[ ⌜ σ ⌝ˢ γ ]
  ⌜ weaken ρ t              ⌝ γ = U.wk ρ (⌜ t ⌝ γ)
  ⌜ subst t σ               ⌝ γ = ⌜ t ⌝ γ U.[ ⌜ σ ⌝ˢ γ ]
  ⌜ var x                   ⌝ _ = U.var x
  ⌜ defn α                  ⌝ _ = U.defn α
  ⌜ U l                     ⌝ γ = U.U (⟦ l ⟧ˡ γ)
  ⌜ Empty                   ⌝ _ = U.Empty
  ⌜ emptyrec p A t          ⌝ γ = U.emptyrec (⟦ p ⟧ᵍ γ) (⌜ A ⌝ γ)
                                    (⌜ t ⌝ γ)
  ⌜ Unit s l                ⌝ γ = U.Unit (⟦ s ⟧ˢ γ) (⟦ l ⟧ˡ γ)
  ⌜ star s l                ⌝ γ = U.star (⟦ s ⟧ˢ γ) (⟦ l ⟧ˡ γ)
  ⌜ unitrec l p q A t₁ t₂   ⌝ γ = U.unitrec (⟦ l ⟧ˡ γ) (⟦ p ⟧ᵍ γ)
                                    (⟦ q ⟧ᵍ γ) (⌜ A ⌝ γ) (⌜ t₁ ⌝ γ)
                                    (⌜ t₂ ⌝ γ)
  ⌜ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ A₂ ⌝ γ = U.ΠΣ⟨ ⟦ b ⟧ᵇᵐ γ ⟩ ⟦ p ⟧ᵍ γ ,
                                    ⟦ q ⟧ᵍ γ ▷ ⌜ A₁ ⌝ γ ▹ ⌜ A₂ ⌝ γ
  ⌜ lam p t                 ⌝ γ = U.lam (⟦ p ⟧ᵍ γ) (⌜ t ⌝ γ)
  ⌜ t₁ ∘⟨ p ⟩ t₂            ⌝ γ = ⌜ t₁ ⌝ γ U.∘⟨ ⟦ p ⟧ᵍ γ ⟩ ⌜ t₂ ⌝ γ
  ⌜ prod s p t₁ t₂          ⌝ γ = U.prod (⟦ s ⟧ˢ γ) (⟦ p ⟧ᵍ γ)
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
  ⌜ rfl                     ⌝ _ = U.rfl
  ⌜ J p q A₁ t₁ A₂ t₂ t₃ t₄ ⌝ γ = U.J (⟦ p ⟧ᵍ γ) (⟦ q ⟧ᵍ γ) (⌜ A₁ ⌝ γ)
                                    (⌜ t₁ ⌝ γ) (⌜ A₂ ⌝ γ) (⌜ t₂ ⌝ γ)
                                    (⌜ t₃ ⌝ γ) (⌜ t₄ ⌝ γ)
  ⌜ K p A₁ t₁ A₂ t₂ t₃      ⌝ γ = U.K (⟦ p ⟧ᵍ γ) (⌜ A₁ ⌝ γ) (⌜ t₁ ⌝ γ)
                                    (⌜ A₂ ⌝ γ) (⌜ t₂ ⌝ γ) (⌜ t₃ ⌝ γ)
  ⌜ []-cong s A t₁ t₂ t₃    ⌝ γ = U.[]-cong (⟦ s ⟧ˢ γ) (⌜ A ⌝ γ)
                                    (⌜ t₁ ⌝ γ) (⌜ t₂ ⌝ γ) (⌜ t₃ ⌝ γ)

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

opaque

  -- The definition of ⌜_⌝ for meta-var includes a special case for
  -- id, intended to make the type-checker a little easier to use.
  -- That special case does not affect the function's result.

  ⌜meta-var⌝ :
    {x : Meta-var c n₁} (σ : Subst c n₂ n₁) →
    ⌜ meta-var x σ ⌝ γ PE.≡ ⌜ x ⌝ᵐ γ U.[ ⌜ σ ⌝ˢ γ ]
  ⌜meta-var⌝ σ with is-id? σ
  … | just id = PE.sym (subst-id _)
  … | nothing = PE.refl

-- Turns definition contexts into regular definition contexts.

⌜_⌝ᶜᵈ : DCon c n → Contexts c → U.DCon (U.Term 0) n
⌜ base nothing      ⌝ᶜᵈ γ = γ .⌜base⌝ .U.defs
⌜ base (just φ)     ⌝ᶜᵈ γ = Trans φ (γ .⌜base⌝ .U.defs)
⌜ ε                 ⌝ᶜᵈ _ = ε
⌜ ∇ ∙⟨ n ⟩[ t ∷ A ] ⌝ᶜᵈ γ = ⌜ ∇ ⌝ᶜᵈ γ ∙⟨ n ⟩[ ⌜ t ⌝ γ ∷ ⌜ A ⌝ γ ]

-- Turns variable contexts into regular variable contexts.

⌜_⌝ᶜᵛ : Con c n → Contexts c → U.Con U.Term n
⌜ base  ⌝ᶜᵛ γ = γ .⌜base⌝ .U.vars
⌜ ε     ⌝ᶜᵛ _ = ε
⌜ Γ ∙ A ⌝ᶜᵛ γ = ⌜ Γ ⌝ᶜᵛ γ ∙ ⌜ A ⌝ γ

-- Turns context pairs into regular context pairs.

⌜_⌝ᶜ : Cons c m n → Contexts c → U.Cons m n
⌜ Γ ⌝ᶜ γ = ⌜ Γ .defs ⌝ᶜᵈ γ » ⌜ Γ .vars ⌝ᶜᵛ γ

------------------------------------------------------------------------
-- Translation from regular contexts

opaque

  -- Turns regular variable contexts into variable contexts.
  --
  -- This definition is opaque because it is only intended to be
  -- applied to contexts that are meta-level variables.

  ⌞_⌟ᶜᵛ : U.Con U.Term n → Con c n
  ⌞ ε     ⌟ᶜᵛ = ε
  ⌞ Γ ∙ A ⌟ᶜᵛ = ⌞ Γ ⌟ᶜᵛ ∙ ⌞ A ⌟ id

opaque
  unfolding ⌞_⌟ᶜᵛ

  -- ⌜_⌝ᶜᵛ δ is a left inverse of ⌞_⌟ᶜᵛ.

  ⌜⌞⌟ᶜᵛ⌝ᶜᵛ : {Γ : U.Con U.Term n} → ⌜ ⌞ Γ ⌟ᶜᵛ ⌝ᶜᵛ γ PE.≡ Γ
  ⌜⌞⌟ᶜᵛ⌝ᶜᵛ {Γ = ε}     = PE.refl
  ⌜⌞⌟ᶜᵛ⌝ᶜᵛ {Γ = _ ∙ _} = PE.cong₂ _∙_ ⌜⌞⌟ᶜᵛ⌝ᶜᵛ (subst-id _)

opaque

  -- Turns regular definition contexts into definition contexts.
  --
  -- This definition is opaque because it is only intended to be
  -- applied to contexts that are meta-level variables.

  ⌞_⌟ᶜᵈ : U.DCon (U.Term 0) n → DCon c n
  ⌞ ε                 ⌟ᶜᵈ = ε
  ⌞ ∇ ∙⟨ o ⟩[ t ∷ A ] ⌟ᶜᵈ =
    ⌞ ∇ ⌟ᶜᵈ ∙⟨ o ⟩[ ⌞ t ⌟ id ∷ ⌞ A ⌟ id ]

opaque
  unfolding ⌞_⌟ᶜᵈ

  -- ⌜_⌝ᶜᵈ γ is a left inverse of ⌞_⌟ᶜᵈ.

  ⌜⌞⌟ᶜᵈ⌝ᶜᵈ : {Γ : U.DCon (U.Term 0) n} → ⌜ ⌞ Γ ⌟ᶜᵈ ⌝ᶜᵈ γ PE.≡ Γ
  ⌜⌞⌟ᶜᵈ⌝ᶜᵈ {Γ = ε}                 = PE.refl
  ⌜⌞⌟ᶜᵈ⌝ᶜᵈ {Γ = _ ∙⟨ _ ⟩[ _ ∷ _ ]} =
    PE.cong₃ _∙⟨ _ ⟩[_∷_] ⌜⌞⌟ᶜᵈ⌝ᶜᵈ (subst-id _) (subst-id _)

opaque

  -- Turns regular context pairs into context triples.
  --
  -- This definition is opaque because it is only intended to be
  -- applied to context pairs that are meta-level variables.

  ⌞_⌟ᶜ : U.Cons m n → Cons c m n
  ⌞ ∇ » Γ ⌟ᶜ = record
    { defs = ⌞ ∇ ⌟ᶜᵈ
    ; vars = ⌞ Γ ⌟ᶜᵛ
    }

opaque
  unfolding ⌞_⌟ᶜ

  -- ⌜_⌝ᶜ γ is a left inverse of ⌞_⌟ᶜ.

  ⌜⌞⌟ᶜ⌝ᶜ : {Γ : U.Cons m n} → ⌜ ⌞ Γ ⌟ᶜ ⌝ᶜ γ PE.≡ Γ
  ⌜⌞⌟ᶜ⌝ᶜ {Γ = _ » _} = PE.cong₂ _»_ ⌜⌞⌟ᶜᵈ⌝ᶜᵈ ⌜⌞⌟ᶜᵛ⌝ᶜᵛ

------------------------------------------------------------------------
-- An abbreviation

-- A variant of the constructor meta-var.

varᵐ : (x : Fin (c .ms)) → Term c (Vec.lookup (c .meta-con-size) x)
varᵐ x = meta-var (var! x) id

opaque

  -- The function varᵐ is correctly implemented.

  ⌜varᵐ⌝ :
    (γ : Contexts c) →
    ⌜ varᵐ x ⌝ γ PE.≡ ⌜ var x PE.refl ⌝ᵐ γ
  ⌜varᵐ⌝ _ = PE.refl

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

Erased : Termˢ (c .ss) → Term c n → Term c n
Erased s A = ΠΣ⟨ BMΣ s ⟩ 𝟘 , 𝟘 ▷ A ▹ Unit s zero

-- The term constructor [_].

box : Termˢ (c .ss) → Term c n → Term c n
box s t = prod s 𝟘 t (star s zero)
