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
infixr 30 _maxᵘ_
infix 25 _[_]
infix 25 _[_]₀
infix 25 _[_]↑
infix 25 _[_,_]₁₀
infix 25 _[_]↑²
infix 25 _[_][_]↑
infix 24 _∙[_][_][_]

------------------------------------------------------------------------
-- The syntax

-- The type of terms is parametrised by the number of free variables.
-- Variables are de Bruijn indices.

data Term (n : Nat) : Set a where
  var : (x : Fin n) → Term n
  Level : Term n
  zeroᵘ : Term n
  sucᵘ : Term n → Term n
  _maxᵘ_ : Term n → Term n → Term n
  U : Term n → Term n
  Lift : (l : Term n) (A : Term n) → Term n
  lift : (a : Term n) → Term n
  lower : (a : Term n) → Term n
  Empty : Term n
  emptyrec : (p : M) (A t : Term n) → Term n
  Unit : Strength → Term n → Term n
  star : Strength → Term n → Term n
  unitrec : (p q : M) → Term n → (A : Term (1+ n))
            (t u : Term n) → Term n
  ΠΣ⟨_⟩_,_▷_▹_ : (b : BinderMode) (p q : M) (A : Term n)
               (B : Term (1+ n)) → Term n
  lam : (p : M) (t : Term (1+ n)) → Term n
  _∘⟨_⟩_ : (t : Term n) (p : M) (u : Term n) → Term n
  prod : Strength → (p : M) (t u : Term n) → Term n
  fst : (p : M) (t : Term n) → Term n
  snd : (p : M) (t : Term n) → Term n
  prodrec : (r p q : M) (A : Term (1+ n)) (t : Term n)
            (u : Term (2+ n)) → Term n
  ℕ : Term n
  zero : Term n
  suc : (t : Term n) → Term n
  natrec : (p q r : M) (A : Term (1+ n)) (z : Term n)
           (s : Term (2+ n)) (t : Term n) → Term n
  Id : (A t u : Term n) → Term n
  rfl : Term n
  J : (p q : M) (A t : Term n) (B : Term (2+ n)) (u v w : Term n) →
      Term n
  K : (p : M) (A t : Term n) (B : Term (1+ n)) (u v : Term n) →
      Term n
  []-cong : Strength → (A t u v : Term n) → Term n

pattern Unit! = Unit _ _
pattern Unitʷ l = Unit 𝕨 l
pattern Unitˢ l = Unit 𝕤 l

pattern Π_,_▷_▹_ p q F G = ΠΣ⟨ BMΠ ⟩ p , q ▷ F ▹ G
pattern Σˢ_,_▷_▹_ p q F G = ΠΣ⟨ BMΣ 𝕤 ⟩ p , q ▷ F ▹ G
pattern Σʷ_,_▷_▹_ p q F G = ΠΣ⟨ BMΣ 𝕨 ⟩ p , q ▷ F ▹ G
pattern Σ_,_▷_▹_ p q F G = ΠΣ⟨ BMΣ _ ⟩ p , q ▷ F ▹ G
pattern Σ⟨_⟩_,_▷_▹_ s p q F G = ΠΣ⟨ BMΣ s ⟩ p , q ▷ F ▹ G

pattern _∘_ t u = t ∘⟨ _ ⟩ u

pattern prodˢ p t u = prod 𝕤 p t u
pattern prodʷ p t u = prod 𝕨 p t u
pattern prod! t u = prod _ _ t u

pattern star! = star _ _
pattern starʷ l = star 𝕨 l
pattern starˢ l = star 𝕤 l

pattern []-cong! A t u v = []-cong _ A t u v
pattern []-congʷ A t u v = []-cong 𝕨 A t u v
pattern []-congˢ A t u v = []-cong 𝕤 A t u v

private variable
  t : Term _

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

sucᵏ : (k : Nat) → Term n
sucᵏ 0      = zero
sucᵏ (1+ n) = suc (sucᵏ n)

-- The canonical level term corresponding to the given natural number.

↓ᵘ_ : Nat → Term n
↓ᵘ 0    = zeroᵘ
↓ᵘ 1+ n = sucᵘ (↓ᵘ n)

------------------------------------------------------------------------
-- An alternative syntax representation


-- Kinds are indexed by a list of natural numbers specifying
-- the number of sub-terms (the length of the list) and the
-- number of new variables bound by each sub-term (each element
-- in the list).

data Kind : (ns : List Nat) → Set a where
  Levelkind : Kind []
  Zeroᵘkind  : Kind []
  Sucᵘkind   : Kind (0 ∷ [])
  Maxᵘkind   : Kind (0 ∷ 0 ∷ [])

  Ukind : Kind (0 ∷ [])

  Liftkind : Kind (0 ∷ 0 ∷ [])
  liftkind : Kind (0 ∷ [])
  lowerkind : Kind (0 ∷ [])

  Emptykind    : Kind []
  Emptyreckind : (p : M) → Kind (0 ∷ 0 ∷ [])

  Unitkind : Strength → Kind (0 ∷ [])
  Starkind : Strength → Kind (0 ∷ [])
  Unitreckind : (p q : M) → Kind (0 ∷ 1 ∷ 0 ∷ 0 ∷ [])

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

  Idkind      : Kind (0 ∷ 0 ∷ 0 ∷ [])
  Reflkind    : Kind []
  Jkind       : M → M → Kind (0 ∷ 0 ∷ 2 ∷ 0 ∷ 0 ∷ 0 ∷ [])
  Kkind       : M → Kind (0 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ [])
  Boxcongkind : Strength → Kind (0 ∷ 0 ∷ 0 ∷ 0 ∷ [])

-- In the alternative term representations, a term is either a
-- variable (de Bruijn index) or a "generic"

-- The alternative term representation is parametrised by the number of
-- free variables. A term is either a variable (a de Bruijn index) or a
-- generic term, consisting of a kind and a list of sub-terms.
--
-- A term (gen k (n₁ ∷ … ∷ nₘ)) consists of m sub-terms (possibly zero)
-- with sub-term i binding nᵢ variables.

data Term′ (n : Nat) : Set a where
  var : (x : Fin n) → Term′ n
  gen : {bs : List Nat} (k : Kind bs) (ts : GenTs Term′ n bs) → Term′ n

private variable
  k k′ : Kind _

-- Converting from the alternative syntax.

toTerm : Term′ n → Term n
toTerm (var x) =
  var x
toTerm (gen Levelkind []) =
  Level
toTerm (gen Zeroᵘkind []) =
  zeroᵘ
toTerm (gen Sucᵘkind (l ∷ₜ [])) =
  sucᵘ (toTerm l)
toTerm (gen Maxᵘkind (l₁ ∷ₜ l₂ ∷ₜ [])) =
  toTerm l₁ maxᵘ toTerm l₂
toTerm (gen Ukind (l ∷ₜ [])) =
  U (toTerm l)
toTerm (gen Liftkind (l ∷ₜ A ∷ₜ [])) =
  Lift (toTerm l) (toTerm A)
toTerm (gen liftkind (a ∷ₜ [])) =
  lift (toTerm a)
toTerm (gen lowerkind (a ∷ₜ [])) =
  lower (toTerm a)
toTerm (gen (Binderkind b p q) (A ∷ₜ B ∷ₜ [])) =
  ΠΣ⟨ b ⟩ p , q ▷ (toTerm A) ▹ (toTerm B)
toTerm (gen (Lamkind p) (t ∷ₜ [])) =
  lam p (toTerm t)
toTerm (gen (Appkind p) (t ∷ₜ u ∷ₜ [])) =
  toTerm t ∘⟨ p ⟩ toTerm u
toTerm (gen (Prodkind s p) (t ∷ₜ u ∷ₜ [])) =
  prod s p (toTerm t) (toTerm u)
toTerm (gen (Fstkind p) (t ∷ₜ [])) =
  fst p (toTerm t)
toTerm (gen (Sndkind p) (t ∷ₜ [])) =
  snd p (toTerm t)
toTerm (gen (Prodreckind r p q) (A ∷ₜ t ∷ₜ u ∷ₜ [])) =
  prodrec r p q (toTerm A) (toTerm t) (toTerm u)
toTerm (gen Natkind []) =
  ℕ
toTerm (gen Zerokind []) =
  zero
toTerm (gen Suckind (t ∷ₜ [])) =
  suc (toTerm t)
toTerm (gen (Natreckind p q r) (A ∷ₜ z ∷ₜ s ∷ₜ n ∷ₜ [])) =
  natrec p q r (toTerm A) (toTerm z) (toTerm s) (toTerm n)
toTerm (gen (Unitkind s) (l ∷ₜ [])) =
  Unit s (toTerm l)
toTerm (gen (Starkind s) (l ∷ₜ [])) =
  star s (toTerm l)
toTerm (gen (Unitreckind p q) (l ∷ₜ A ∷ₜ t ∷ₜ u ∷ₜ [])) =
  unitrec p q (toTerm l) (toTerm A) (toTerm t) (toTerm u)
toTerm (gen Emptykind []) =
  Empty
toTerm (gen (Emptyreckind p) (A ∷ₜ t ∷ₜ [])) =
  emptyrec p (toTerm A) (toTerm t)
toTerm (gen Idkind (A ∷ₜ t ∷ₜ u ∷ₜ [])) =
  Id (toTerm A) (toTerm t) (toTerm u)
toTerm (gen Reflkind []) =
  rfl
toTerm (gen (Jkind p q) (A ∷ₜ t ∷ₜ B ∷ₜ u ∷ₜ v ∷ₜ w ∷ₜ [])) =
  J p q (toTerm A) (toTerm t) (toTerm B) (toTerm u) (toTerm v) (toTerm w)
toTerm (gen (Kkind p) (A ∷ₜ t ∷ₜ B ∷ₜ u ∷ₜ v ∷ₜ [])) =
  K p (toTerm A) (toTerm t) (toTerm B) (toTerm u) (toTerm v)
toTerm (gen (Boxcongkind s) (A ∷ₜ t ∷ₜ u ∷ₜ v ∷ₜ [])) =
  []-cong s (toTerm A) (toTerm t) (toTerm u) (toTerm v)

-- Converting to the alternative syntax.

fromTerm : Term n → Term′ n
fromTerm (var x) =
  var x
fromTerm Level =
  gen Levelkind []
fromTerm zeroᵘ =
  gen Zeroᵘkind []
fromTerm (sucᵘ l) =
  gen Sucᵘkind (fromTerm l ∷ₜ [])
fromTerm (l₁ maxᵘ l₂) =
  gen Maxᵘkind (fromTerm l₁ ∷ₜ fromTerm l₂ ∷ₜ [])
fromTerm (U l) =
  gen Ukind (fromTerm l ∷ₜ [])
fromTerm (Lift l A) =
  gen Liftkind (fromTerm l ∷ₜ fromTerm A ∷ₜ [])
fromTerm (lift a) =
  gen liftkind (fromTerm a ∷ₜ [])
fromTerm (lower a) =
  gen lowerkind (fromTerm a ∷ₜ [])
fromTerm (ΠΣ⟨ b ⟩ p , q ▷ A ▹ B) =
  gen (Binderkind b p q) (fromTerm A ∷ₜ fromTerm B ∷ₜ [])
fromTerm (lam p t) =
  gen (Lamkind p) (fromTerm t ∷ₜ [])
fromTerm (t ∘⟨ p ⟩ u) =
  gen (Appkind p) (fromTerm t ∷ₜ fromTerm u ∷ₜ [])
fromTerm (prod s p t u) =
  gen (Prodkind s p) (fromTerm t ∷ₜ fromTerm u ∷ₜ [])
fromTerm (fst p t) =
  gen (Fstkind p) (fromTerm t ∷ₜ [])
fromTerm (snd p t) =
  gen (Sndkind p) (fromTerm t ∷ₜ [])
fromTerm (prodrec r p q A t u) =
  gen (Prodreckind r p q)
    (fromTerm A ∷ₜ fromTerm t ∷ₜ fromTerm u ∷ₜ [])
fromTerm ℕ =
  gen Natkind []
fromTerm zero =
  gen Zerokind []
fromTerm (suc t) =
  gen Suckind (fromTerm t ∷ₜ [])
fromTerm (natrec p q r A z s n) =
  gen (Natreckind p q r)
    (fromTerm A ∷ₜ fromTerm z ∷ₜ fromTerm s ∷ₜ fromTerm n ∷ₜ [])
fromTerm (Unit s l) =
  gen (Unitkind s) (fromTerm l ∷ₜ [])
fromTerm (star s l) =
  gen (Starkind s) (fromTerm l ∷ₜ [])
fromTerm (unitrec p q l A t u) =
  gen (Unitreckind p q)
    (fromTerm l ∷ₜ fromTerm A ∷ₜ fromTerm t ∷ₜ fromTerm u ∷ₜ [])
fromTerm Empty =
  gen Emptykind []
fromTerm (emptyrec p A t) =
  gen (Emptyreckind p) (fromTerm A ∷ₜ fromTerm t ∷ₜ [])
fromTerm (Id A t u) =
  gen Idkind (fromTerm A ∷ₜ fromTerm t ∷ₜ fromTerm u ∷ₜ [])
fromTerm rfl =
  gen Reflkind []
fromTerm (J p q A t B u v w) =
  gen (Jkind p q)
    (fromTerm A ∷ₜ fromTerm t ∷ₜ fromTerm B ∷ₜ fromTerm u
                ∷ₜ fromTerm v ∷ₜ fromTerm w ∷ₜ [])
fromTerm (K p A t B u v) =
  gen (Kkind p)
    (fromTerm A ∷ₜ fromTerm t ∷ₜ fromTerm B
                ∷ₜ fromTerm u ∷ₜ fromTerm v ∷ₜ [])
fromTerm ([]-cong s A t u v) =
  gen (Boxcongkind s)
    (fromTerm A ∷ₜ fromTerm t ∷ₜ fromTerm u
                ∷ₜ fromTerm v ∷ₜ [])

------------------------------------------------------------------------
-- Weakening

-- Weakening of terms.
-- If η : Γ ≤ Δ and Δ ⊢ t : A then Γ ⊢ wk η t : wk η A.

wk : (ρ : Wk m n) (t : Term n) → Term m
wk ρ (var x) = var (wkVar ρ x)
wk ρ Level = Level
wk ρ zeroᵘ = zeroᵘ
wk ρ (sucᵘ l) = sucᵘ (wk ρ l)
wk ρ (l₁ maxᵘ l₂) = wk ρ l₁ maxᵘ wk ρ l₂
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
wk ρ (Unit s l) = Unit s (wk ρ l)
wk ρ (star s l) = star s (wk ρ l)
wk ρ (unitrec p q l A t u) =
  unitrec p q (wk ρ l) (wk (lift ρ) A) (wk ρ t) (wk ρ u)
wk ρ Empty = Empty
wk ρ (emptyrec p A t) = emptyrec p (wk ρ A) (wk ρ t)
wk ρ (Id A t u) = Id (wk ρ A) (wk ρ t) (wk ρ u)
wk ρ rfl = rfl
wk ρ (J p q A t B u v w) =
  J p q (wk ρ A) (wk ρ t) (wk (liftn ρ 2) B) (wk ρ u) (wk ρ v) (wk ρ w)
wk ρ (K p A t B u v) =
  K p (wk ρ A) (wk ρ t) (wk (lift ρ) B) (wk ρ u) (wk ρ v)
wk ρ ([]-cong s A t u v) =
  []-cong s (wk ρ A) (wk ρ t) (wk ρ u) (wk ρ v)

-- Weakening for the alternative term representation.

mutual

  wkGen : {m n : Nat} {bs : List Nat} (ρ : Wk m n)
          (c : GenTs Term′ n bs) → GenTs Term′ m bs
  wkGen ρ []                 = []
  wkGen ρ (_∷ₜ_ {b = b} t c) = wk′ (liftn ρ b) t ∷ₜ wkGen ρ c

  wk′ : (ρ : Wk m n) (t : Term′ n) → Term′ m
  wk′ ρ (var x) = var (wkVar ρ x)
  wk′ ρ (gen k ts) = gen k (wkGen ρ ts)

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

-- The function wk[ k ] applies wk1 k times.

wk[_] : ∀ k → Term n → Term (k + n)
wk[ 0    ] t = t
wk[ 1+ k ] t = wk1 (wk[ k ] t)

-- An alternative to wk[_].

wk[_]′ : ∀ k → Term n → Term (k + n)
wk[ k ]′ = wk (stepn id k)

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

_[_] : (t : Term n) (σ : Subst m n) → Term m
var x [ σ ] = σ x
Level [ σ ] = Level
zeroᵘ [ σ ] = zeroᵘ
sucᵘ l [ σ ] = sucᵘ (l [ σ ])
l₁ maxᵘ l₂ [ σ ] = (l₁ [ σ ]) maxᵘ (l₂ [ σ ])
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
Unit s l [ σ ] = Unit s (l [ σ ])
star s l [ σ ] = star s (l [ σ ])
unitrec p q l A t u [ σ ] =
  unitrec p q (l [ σ ]) (A [ σ ⇑ ]) (t [ σ ]) (u [ σ ])
Empty [ σ ] = Empty
emptyrec p A t [ σ ] = emptyrec p (A [ σ ]) (t [ σ ])
Id A t u [ σ ] = Id (A [ σ ]) (t [ σ ]) (u [ σ ])
rfl [ σ ] = rfl
J p q A t B u v w [ σ ] =
  J p q (A [ σ ]) (t [ σ ]) (B [ σ ⇑[ 2 ] ]) (u [ σ ]) (v [ σ ])
    (w [ σ ])
K p A t B u v [ σ ] =
  K p (A [ σ ]) (t [ σ ]) (B [ σ ⇑ ]) (u [ σ ]) (v [ σ ])
[]-cong s A t u v [ σ ] =
  []-cong s (A [ σ ]) (t [ σ ]) (u [ σ ]) (v [ σ ])

-- Substitution for the alternative term representation.

mutual
  substGen : {bs : List Nat} (σ : Subst m n)
             (ts : GenTs Term′ n bs) → GenTs Term′ m bs
  substGen σ []              = []
  substGen σ (_∷ₜ_ {b} t ts) = t [ liftSubstn σ b ]′ ∷ₜ substGen σ ts

  _[_]′ : (t : Term′ n) (σ : Subst m n) → Term′ m
  var x [ σ ]′ = fromTerm (σ x)
  gen k ts [ σ ]′ = gen k (substGen σ ts)

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
-- If Γ∙A∙B ⊢ t : C, Γ ⊢ s : A and Γ ⊢ s′ : B then Γ ⊢ t[s,s′] : C[s,s′]

_[_,_]₁₀ : (t : Term (2+ n)) (s s′ : Term n) → Term n
t [ s , s′ ]₁₀ = t [ consSubst (sgSubst s) s′ ]

-- Substitute the first variable with a term and shift remaining
-- variables up by one
-- If Γ ∙ A ⊢ t : A′ and Γ ∙ B ∙ C ⊢ s : A then Γ ∙ B ∙ C ⊢ t[s]↑² : A′

_[_]↑² : (t : Term (1+ n)) (s : Term (2+ n)) → Term (2+ n)
t [ s ]↑² = t [ consSubst (wk1Subst (wk1Subst idSubst)) s ]

-- A generalisation of _[_]↑ and _[_]↑².

_[_][_]↑ : Term (1+ n) → ∀ k → Term (k + n) → Term (k + n)
t [ k ][ u ]↑ = t [ consSubst (wkSubst k idSubst) u ]

-- Δ ∙[ k ][ Γ ][ σ ] is Δ extended with the last k elements of Γ,
-- modified using σ (suitably lifted).

_∙[_][_][_] :
  Con Term m → ∀ k → Con Term (k + n) → Subst m n → Con Term (k + m)
Δ ∙[ 0    ][ _     ][ _ ] = Δ
Δ ∙[ 1+ k ][ Γ ∙ A ][ σ ] = Δ ∙[ k ][ Γ ][ σ ] ∙ A [ σ ⇑[ k ] ]

------------------------------------------------------------------------
-- Some inversion lemmas

-- Inversion of equality for gen.

gen-cong⁻¹ :
  gen {bs = bs} k ts ≡ gen {bs = bs′} k′ ts′ →
  ∃ λ (eq : bs ≡ bs′) →
    PE.subst Kind eq k ≡ k′ ×
    PE.subst (GenTs Term′ _) eq ts ≡ ts′
gen-cong⁻¹ refl = refl , refl , refl

-- Inversion of equality for _∷ₜ_.

∷-cong⁻¹ :
  ∀ {b} {t t′ : Term′ (b + n)} →
  _∷ₜ_ {A = Term′} {b = b} t ts ≡ t′ ∷ₜ ts′ →
  t ≡ t′ × ts ≡ ts′
∷-cong⁻¹ refl = refl , refl
