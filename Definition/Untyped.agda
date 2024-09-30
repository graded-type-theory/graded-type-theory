------------------------------------------------------------------------
-- Raw terms, weakening (renaming) and substitution.
------------------------------------------------------------------------

module Definition.Untyped {a} (M : Set a) where

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
open import Tools.List
open import Tools.PropositionalEquality as PE hiding (subst)

-- Some definitions that do not depend on M are re-exported from
-- Definition.Untyped.NotParametrised.

open import Definition.Untyped.NotParametrised public

private
  variable
    n m l : Nat
    bs bs′ : List _
    ts ts′ : GenTs _ _ _

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
infix 25 _[_]
infix 25 _[_]₀
infix 25 _[_]↑
infix 25 _[_,_]₁₀
infix 25 _[_]↑²

-- Kinds are indexed by a list of natural numbers specifying
-- the number of sub-terms (the length of the list) and the
-- number of new variables bound by each sub-term (each element
-- in the list).

data Kind : (ns : List Nat) → Set a where
  Ukind : Universe-level → Kind []

  Binderkind : (b : BinderMode) (p q : M) → Kind (0 ∷ 1 ∷ [])

  Lamkind : (p : M)   → Kind (1 ∷ [])
  Appkind : (p : M)   → Kind (0 ∷ 0 ∷ [])

  Prodkind    : Strength → (p : M) → Kind (0 ∷ 0 ∷ [])
  Fstkind     : (p : M) → Kind (0 ∷ [])
  Sndkind     : (p : M) → Kind (0 ∷ [])
  Prodreckind : (r p q : M) → Kind (1 ∷ 0 ∷ 2 ∷ [])

  Natkind    : Kind []
  Zerokind   : Kind []
  Suckind    : Kind (0 ∷ [])
  Natreckind : (p q r : M) → Kind (1 ∷ 0 ∷ 2 ∷ 0 ∷ [])

  Unitkind : Strength → Universe-level → Kind []
  Starkind : Strength → Universe-level → Kind []
  Unitreckind : Universe-level → (p q : M) → Kind (1 ∷ 0 ∷ 0 ∷ [])

  Emptykind    : Kind []
  Emptyreckind : (p : M) → Kind (0 ∷ 0 ∷ [])

  Idkind      : Kind (0 ∷ 0 ∷ 0 ∷ [])
  Reflkind    : Kind []
  Jkind       : M → M → Kind (0 ∷ 0 ∷ 2 ∷ 0 ∷ 0 ∷ 0 ∷ [])
  Kkind       : M → Kind (0 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ [])
  Boxcongkind : Strength → Kind (0 ∷ 0 ∷ 0 ∷ 0 ∷ [])

-- The type of terms is parametrised by the number of free variables.
-- A term is either a variable (a de Bruijn index) or a generic term,
-- consisting of a kind and a list of sub-terms.
--
-- A term (gen k (n₁ ∷ … ∷ nₘ)) consists of m sub-terms (possibly zero)
-- each binding nᵢ variables.

data Term (n : Nat) : Set a where
  var : (x : Fin n) → Term n
  gen : {bs : List Nat} (k : Kind bs) (ts : GenTs Term n bs) → Term n

private variable
  t    : Term n
  k k′ : Kind _

-- The Grammar of our language.

-- We represent the expressions of our language as de Bruijn terms.
-- Variables are natural numbers interpreted as de Bruijn indices.
-- Π, lam, and natrec are binders.

-- Type constructors.
pattern U n = gen (Ukind n) []
pattern ℕ = gen Natkind []
pattern Empty = gen Emptykind []
pattern Unit! = gen (Unitkind _ _) []
pattern Unit s l = gen (Unitkind s l) []
pattern Unitʷ l = gen (Unitkind 𝕨 l) []
pattern Unitˢ l = gen (Unitkind 𝕤 l) []

pattern ΠΣ⟨_⟩_,_▷_▹_ b p q F G = gen (Binderkind b p q) (F ∷ₜ G ∷ₜ [])
pattern Π_,_▷_▹_ p q F G = gen (Binderkind BMΠ p q) (F ∷ₜ G ∷ₜ [])
pattern Σˢ_,_▷_▹_ p q F G = gen (Binderkind (BMΣ 𝕤) p q) (F ∷ₜ G ∷ₜ [])
pattern Σʷ_,_▷_▹_ p q F G = gen (Binderkind (BMΣ 𝕨) p q) (F ∷ₜ G ∷ₜ [])
pattern Σ_,_▷_▹_ p q F G = gen (Binderkind (BMΣ _) p q) (F ∷ₜ G ∷ₜ [])
pattern Σ⟨_⟩_,_▷_▹_ s p q F G =
  gen (Binderkind (BMΣ s) p q) (F ∷ₜ G ∷ₜ [])

pattern lam p t = gen (Lamkind p) (t ∷ₜ [])
pattern _∘⟨_⟩_ t p u = gen (Appkind p) (t ∷ₜ u ∷ₜ [])
pattern _∘_ t u = gen (Appkind _) (t ∷ₜ u ∷ₜ [])

pattern prodˢ p t u = gen (Prodkind 𝕤 p) (t ∷ₜ u ∷ₜ [])
pattern prodʷ p t u = gen (Prodkind 𝕨 p) (t ∷ₜ u ∷ₜ [])
pattern prod m p t u = gen (Prodkind m p) (t ∷ₜ u ∷ₜ [])
pattern prod! t u = gen (Prodkind _ _) (t ∷ₜ u ∷ₜ [])
pattern fst p t = gen (Fstkind p) (t ∷ₜ [])
pattern snd p t = gen (Sndkind p) (t ∷ₜ [])
pattern prodrec r p q A t u =
  gen (Prodreckind r p q) (A ∷ₜ t ∷ₜ u ∷ₜ [])

pattern zero = gen Zerokind []
pattern suc t = gen Suckind (t ∷ₜ [])
pattern natrec p q r A z s n =
  gen (Natreckind p q r) (A ∷ₜ z ∷ₜ s ∷ₜ n ∷ₜ [])

pattern star! = gen (Starkind _ _) []
pattern star s l = gen (Starkind s l) []
pattern starʷ l = gen (Starkind 𝕨 l) []
pattern starˢ l = gen (Starkind 𝕤 l) []
pattern unitrec l p q A t u =
  gen (Unitreckind l p q) (A ∷ₜ t ∷ₜ u ∷ₜ [])
pattern emptyrec p A t = gen (Emptyreckind p) (A ∷ₜ t ∷ₜ [])

pattern Id A t u = gen Idkind (A ∷ₜ t ∷ₜ u ∷ₜ [])
pattern rfl = gen Reflkind []
pattern J p q A t B u v w =
  gen (Jkind p q) (A ∷ₜ t ∷ₜ B ∷ₜ u ∷ₜ v ∷ₜ w ∷ₜ [])
pattern K p A t B u v = gen (Kkind p) (A ∷ₜ t ∷ₜ B ∷ₜ u ∷ₜ v ∷ₜ [])
pattern []-cong! A t u v = gen (Boxcongkind _) (A ∷ₜ t ∷ₜ u ∷ₜ v ∷ₜ [])
pattern []-cong m A t u v = gen (Boxcongkind m) (A ∷ₜ t ∷ₜ u ∷ₜ v ∷ₜ [])
pattern []-congʷ A t u v = gen (Boxcongkind 𝕨) (A ∷ₜ t ∷ₜ u ∷ₜ v ∷ₜ [])
pattern []-congˢ A t u v = gen (Boxcongkind 𝕤) (A ∷ₜ t ∷ₜ u ∷ₜ v ∷ₜ [])


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

sucᵏ : (k : Nat) → Term n
sucᵏ 0      = zero
sucᵏ (1+ n) = suc (sucᵏ n)

------------------------------------------------------------------------
-- Weakening

  -- Weakening of terms.
  -- If η : Γ ≤ Δ and Δ ⊢ t : A then Γ ⊢ wk η t : wk η A.

mutual
  wkGen : {m n : Nat} {bs : List Nat} (ρ : Wk m n) (c : GenTs (Term) n bs) → GenTs (Term) m bs
  wkGen ρ []                 = []
  wkGen ρ (_∷ₜ_ {b = b} t c) = wk (liftn ρ b) t ∷ₜ wkGen ρ c

  wk : {m n : Nat} (ρ : Wk m n) (t : Term n) → Term m
  wk ρ (var x)   = var (wkVar ρ x)
  wk ρ (gen k c) = gen k (wkGen ρ c)


-- Adding one variable to the context requires wk1.
-- If Γ ⊢ t : B then Γ∙A ⊢ wk1 t : wk1 B.

wk1 : Term n → Term (1+ n)
wk1 = wk (step id)

-- Two successive uses of wk1.

wk2 : Term n → Term (1+ (1+ n))
wk2 = wk1 ∘→ wk1

-- An alternative to wk2.

wk₂ : Term n → Term (2+ n)
wk₂ = wk (step (step id))

-- Three successive uses of wk1.

wk3 : Term n → Term (3+ n)
wk3 = wk1 ∘→ wk2

-- An alternative to wk3.

wk₃ : Term n → Term (3+ n)
wk₃ = wk (step (step (step id)))




------------------------------------------------------------------------
-- Substitution

-- The substitution operation t [ σ ] replaces the free de Bruijn indices
-- of term t by chosen terms as specified by σ.

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

-- Transform a weakening into a substitution.
--
-- If ρ : Γ ≤ Δ then Γ ⊢ toSubst ρ : Δ.

toSubst :  Wk m n → Subst m n
toSubst pr x = var (wkVar pr x)

-- Apply a substitution to a term.
--
-- If Γ ⊢ σ : Δ and Δ ⊢ t : A then Γ ⊢ t [ σ ] : A [ σ ].

mutual
  substGen : {bs : List Nat} (σ : Subst m n) (g : GenTs (Term) n bs) → GenTs (Term) m bs
  substGen σ []              = []
  substGen σ (_∷ₜ_ {b} t ts) = t [ liftSubstn σ b ] ∷ₜ substGen σ ts

  _[_] : (t : Term n) (σ : Subst m n) → Term m
  var x [ σ ] = substVar σ x
  gen x c [ σ ] = gen x (substGen σ c)

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

-- Compose two substitutions.
--
-- If Γ ⊢ σ : Δ and Δ ⊢ σ′ : Φ then Γ ⊢ σ ₛ•ₛ σ′ : Φ.

_ₛ•ₛ_ : Subst l m → Subst m n → Subst l n
_ₛ•ₛ_ σ σ′ x = σ′ x [ σ ]

-- Composition of weakening and substitution.
--
--  If ρ : Γ ≤ Δ and Δ ⊢ σ : Φ then Γ ⊢ ρ •ₛ σ : Φ.

_•ₛ_ : Wk l m → Subst m n → Subst l n
_•ₛ_ ρ σ x = wk ρ (σ x)

--  If Γ ⊢ σ : Δ and ρ : Δ ≤ Φ then Γ ⊢ σ ₛ• ρ : Φ.

_ₛ•_ : Subst l m → Wk m n → Subst l n
_ₛ•_ σ ρ x = σ (wkVar ρ x)

-- Substitute the first variable of a term with an other term.
--
-- If Γ∙A ⊢ t : B and Γ ⊢ s : A then Γ ⊢ t[s]₀ : B[s]₀.

_[_]₀ : (t : Term (1+ n)) (s : Term n) → Term n
t [ s ]₀ = t [ sgSubst s ]

-- Substitute the first variable of a term with an other term,
-- but let the two terms share the same context.
--
-- If Γ∙A ⊢ t : B and Γ∙A ⊢ s : A then Γ∙A ⊢ t[s]↑ : B[s]↑.

_[_]↑ : (t : Term (1+ n)) (s : Term (1+ n)) → Term (1+ n)
t [ s ]↑ = t [ consSubst (wk1Subst idSubst) s ]


-- Substitute the first two variables of a term with other terms.
--
-- If Γ∙A∙B ⊢ t : C, Γ ⊢ s : A and Γ ⊢ s′ : B and  then Γ ⊢ t[s,s′] : C[s,s′]

_[_,_]₁₀ : (t : Term (2+ n)) (s s′ : Term n) → Term n
t [ s , s′ ]₁₀ = t [ consSubst (sgSubst s) s′ ]

-- Substitute the first variable with a term and shift remaining variables up by one
-- If Γ ∙ A ⊢ t : A′ and Γ ∙ B ∙ C ⊢ s : A then Γ ∙ B ∙ C ⊢ t[s]↑² : A′

_[_]↑² : (t : Term (1+ n)) (s : Term (2+ n)) → Term (2+ n)
t [ s ]↑² = t [ consSubst (wk1Subst (wk1Subst idSubst)) s ]


B-subst : (σ : Subst m n) (W : BindingType) (F : Term n) (G : Term (1+ n))
        → (⟦ W ⟧ F ▹ G) [ σ ] PE.≡ ⟦ W ⟧ F [ σ ] ▹ (G [ liftSubst σ ])
B-subst σ (BΠ p q) F G = PE.refl
B-subst σ (BΣ m p q) F G = PE.refl

------------------------------------------------------------------------
-- Some inversion lemmas

-- Inversion of equality for gen.

gen-cong⁻¹ :
  gen {bs = bs} k ts ≡ gen {bs = bs′} k′ ts′ →
  ∃ λ (eq : bs ≡ bs′) →
    PE.subst Kind eq k ≡ k′ ×
    PE.subst (GenTs Term _) eq ts ≡ ts′
gen-cong⁻¹ refl = refl , refl , refl

-- Inversion of equality for _∷_.

∷-cong⁻¹ :
  ∀ {b} {t t′ : Term (b + n)} →
  _∷ₜ_ {A = Term} {b = b} t ts ≡ t′ ∷ₜ ts′ →
  t ≡ t′ × ts ≡ ts′
∷-cong⁻¹ refl = refl , refl
