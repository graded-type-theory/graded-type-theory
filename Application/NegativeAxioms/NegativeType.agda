------------------------------------------------------------------------
-- Negative types (types for which all branches end in ⊥).
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Application.NegativeAxioms.NegativeType
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.Untyped M as U

open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Substitution R
open import Definition.Typed.Weakening R as T
open import Definition.Typed.Consequences.Inequality R as I
open import Definition.Typed.Consequences.Injectivity R

open import Tools.Empty
open import Tools.Function
open import Tools.Nat
open import Tools.Product
open import Tools.Relation

-- Preliminaries
---------------------------------------------------------------------------

private
  Ty  = Term
  Cxt = Con Ty
  variable
    m m'  : Nat
    ρ     : Wk m m'
    σ     : Subst m m'
    Γ Δ   : Con Term m
    A B C : Term m
    t u   : Term m
    p q   : M
    s     : Strength
    l     : Universe-level

-- Negative types
---------------------------------------------------------------------------

-- A type is negative if all of its branches end in ⊥ or U l.
-- The prime example is negation ¬A.

data NegativeType (Γ : Cxt m) : Ty m → Set a where

  empty : NegativeType Γ Empty

  pi    : Γ ⊢ A
        → NegativeType (Γ ∙ A) B
        → NegativeType Γ (Π p , q ▷ A ▹ B)

  sigma : Γ ⊢ A
        → NegativeType Γ A
        → NegativeType (Γ ∙ A) B
        → NegativeType Γ (Σˢ p , q ▷ A ▹ B)

  universe : NegativeType Γ (U l)

  conv  : NegativeType Γ A
        → Γ ⊢ A ≡ B
        → NegativeType Γ B

-- Lemma: Negative types are closed under weakening.

wkNeg : ρ ∷ʷ Δ ⊇ Γ → NegativeType Γ A → NegativeType Δ (U.wk ρ A)

wkNeg w empty
  = empty

wkNeg w (pi dA nB)
  = pi dA' (wkNeg (liftʷʷ w dA') nB)
    where dA' = T.wk w dA

wkNeg w (sigma dA nA nB)
  = sigma dA' (wkNeg w nA) (wkNeg (liftʷʷ w dA') nB)
    where dA' = T.wk w dA

wkNeg _ universe = universe

wkNeg w (conv n c)
  = conv (wkNeg w n) (wkEq w c)

-- Lemma: Negative types are closed under parallel substitution.

subNeg : NegativeType Γ A → Δ ⊢ˢʷ σ ∷ Γ → NegativeType Δ (A [ σ ])

subNeg empty _ = empty

subNeg (pi ⊢A n) s
  = pi (subst-⊢ ⊢A s) (subNeg n (⊢ˢʷ∷-⇑′ ⊢A s))

subNeg (sigma ⊢A nA nB) s
  = sigma (subst-⊢ ⊢A s) (subNeg nA s) (subNeg nB (⊢ˢʷ∷-⇑′ ⊢A s))

subNeg universe _ = universe

subNeg (conv n c) s = conv (subNeg n s) (subst-⊢≡ c (refl-⊢ˢʷ≡∷ s))

-- Corollary: Negative types are closed under single substitution.

subNeg1 : NegativeType (Γ ∙ A) B → Γ ⊢ t ∷ A → NegativeType Γ (B [ t ]₀)
subNeg1 n ⊢t = subNeg n (⊢ˢʷ∷-sgSubst ⊢t)

-- Lemma: The first component of a negative Σ-type is negative.

fstNeg :
  NegativeType Γ C →
  Γ ⊢ C ≡ Σˢ p , q ▷ A ▹ B →
  NegativeType Γ A
fstNeg empty          c = ⊥-elim (Empty≢ΠΣⱼ c)
fstNeg (pi _ _)       c = ⊥-elim (Π≢Σⱼ c)
fstNeg (sigma _ nA _) c = conv nA (proj₁ (Σ-injectivity c))
fstNeg universe       c = ⊥-elim (U≢ΠΣⱼ c)
fstNeg (conv n c)    c' = fstNeg n (trans c c')

-- Lemma: Any instance of the second component of a negative Σ-type is negative.

sndNeg :
  NegativeType Γ C →
  Γ ⊢ C ≡ Σˢ p , q ▷ A ▹ B →
  Γ ⊢ t ∷ A →
  NegativeType Γ (B [ t ]₀)
sndNeg empty          c = ⊥-elim (Empty≢ΠΣⱼ c)
sndNeg (pi _ _)       c = ⊥-elim (Π≢Σⱼ c)
sndNeg (sigma _ _ nB) c ⊢t = let (cA , cB , _ , _) = Σ-injectivity c in
    subNeg (conv nB cB) (⊢ˢʷ∷-sgSubst (conv ⊢t (sym cA)))
sndNeg universe      c  = ⊥-elim (U≢ΠΣⱼ c)
sndNeg (conv n c)    c' = sndNeg n (trans c c')

-- Lemma: Any instance of the codomain of a negative Π-type is negative.

appNeg : NegativeType Γ C → Γ ⊢ C ≡ Π p , q ▷ A ▹ B → Γ ⊢ t ∷ A → NegativeType Γ (B [ t ]₀)
appNeg empty          c = ⊥-elim (Empty≢ΠΣⱼ c)
appNeg (sigma _ _ _)  c = ⊥-elim (Π≢Σⱼ (sym c))
appNeg (pi _ nB) c ⊢t = let (cA , cB , _ , _) = injectivity c in
  subNeg (conv nB cB) (⊢ˢʷ∷-sgSubst (conv ⊢t (sym cA)))
appNeg universe      c  = ⊥-elim (U≢ΠΣⱼ c)
appNeg (conv n c)    c' = appNeg n (trans c c')

-- Lemma: The type ℕ is not negative.

¬negℕ : NegativeType Γ C → Γ ⊢ C ≡ ℕ → ⊥
¬negℕ empty         c = ℕ≢Emptyⱼ (sym c)
¬negℕ (pi _ _)      c = ℕ≢ΠΣⱼ (sym c)
¬negℕ (sigma _ _ _) c = ℕ≢ΠΣⱼ (sym c)
¬negℕ universe      c = U≢ℕ c
¬negℕ (conv n c)   c' = ¬negℕ n (trans c c')

-- Lemma: The type Σʷ is not negative

¬negΣʷ : NegativeType Γ C → Γ ⊢ C ≡ Σʷ p , q ▷ A ▹ B → ⊥
¬negΣʷ empty         c = Empty≢ΠΣⱼ c
¬negΣʷ (pi _ _)      c = Π≢Σⱼ c
¬negΣʷ (sigma _ _ _) c = Σˢ≢Σʷⱼ c
¬negΣʷ universe      c = U≢ΠΣⱼ c
¬negΣʷ (conv n c)   c' = ¬negΣʷ n (trans c c')

-- Lemma: Unit types are not negative.

¬negUnit : NegativeType Γ C → Γ ⊢ C ≡ Unit s l → ⊥
¬negUnit empty c = Empty≢Unitⱼ c
¬negUnit (pi _ _) c = Unit≢ΠΣⱼ (sym c)
¬negUnit (sigma _ _ _) c = Unit≢ΠΣⱼ (sym c)
¬negUnit universe      c = U≢Unitⱼ c
¬negUnit (conv n c) c′ = ¬negUnit n (trans c c′)

opaque

  -- Identity types are not negative.

  ¬negId : NegativeType Γ A → ¬ Γ ⊢ A ≡ Id B t u
  ¬negId empty         = Id≢Empty ∘→ sym
  ¬negId (pi _ _)      = I.Id≢ΠΣ ∘→ sym
  ¬negId (sigma _ _ _) = I.Id≢ΠΣ ∘→ sym
  ¬negId universe      = I.Id≢U ∘→ sym
  ¬negId (conv n B≡A)  = ¬negId n ∘→ trans B≡A
