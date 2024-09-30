------------------------------------------------------------------------
-- Negative types (with support for erasure)
------------------------------------------------------------------------

open import Graded.Modality
open import Definition.Typed.Restrictions

module Application.NegativeOrErasedAxioms.NegativeOrErasedType
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Modality 𝕄

open import Definition.Untyped M as U

open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Weakening R as T
open import Definition.Typed.Consequences.Inequality R as I
open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.Consequences.Substitution R

open import Tools.Empty
open import Tools.Function
open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality using (_≢_)
open import Tools.Relation

private variable
  m n   : Nat
  ρ     : Wk m n
  σ     : Subst m n
  Γ Δ   : Con Term m
  A B C : Term m
  t u   : Term m
  l     : Universe-level
  p q   : M

-- Negative types.

data NegativeType (Γ : Con Term m) : Term m → Set a where
  empty : NegativeType Γ Empty

  pi : Γ ⊢ A →
       NegativeType (Γ ∙ A) B →
       NegativeType Γ (Π p , q ▷ A ▹ B)

  sigma-𝟘 : Γ ⊢ A →
            NegativeType (Γ ∙ A) B →
            NegativeType Γ (Σˢ 𝟘 , q ▷ A ▹ B)

  sigma : Γ ⊢ A →
          NegativeType Γ A →
          NegativeType (Γ ∙ A) B →
          NegativeType Γ (Σˢ p , q ▷ A ▹ B)

  conv  : NegativeType Γ A →
          Γ ⊢ A ≡ B →
          NegativeType Γ B

-- Negative types are closed under weakening.

wkNeg : ρ ∷ Δ ⊇ Γ → ⊢ Δ → NegativeType Γ A → NegativeType Δ (U.wk ρ A)
wkNeg w ⊢Δ empty =
  empty

wkNeg w ⊢Δ (pi dA nB) =
  pi dA′ (wkNeg (lift w) (⊢Δ ∙ dA′) nB)
  where dA′ = T.wk w ⊢Δ dA

wkNeg w ⊢Δ (sigma-𝟘 dA nB) =
  sigma-𝟘 dA′ (wkNeg (lift w) (⊢Δ ∙ dA′) nB)
  where dA′ = T.wk w ⊢Δ dA

wkNeg w ⊢Δ (sigma dA nA nB) =
  sigma dA′ (wkNeg w ⊢Δ nA) (wkNeg (lift w) (⊢Δ ∙ dA′) nB)
  where dA′ = T.wk w ⊢Δ dA

wkNeg w ⊢Δ (conv n c) =
  conv (wkNeg w ⊢Δ n) (wkEq w ⊢Δ c)

-- Negative types are closed under parallel substitution.

subNeg :
  NegativeType Γ A → Δ ⊢ˢ σ ∷ Γ → ⊢ Δ → NegativeType Δ (A [ σ ])

subNeg empty _ _ = empty

subNeg (pi ⊢A n) s ⊢Δ =
  pi ⊢σA (subNeg n (liftSubst′ (wf ⊢A) ⊢Δ ⊢A s) (⊢Δ ∙ ⊢σA))
  where ⊢σA = substitution ⊢A s ⊢Δ

subNeg (sigma-𝟘 ⊢A n) s ⊢Δ =
  sigma-𝟘 ⊢σA (subNeg n (liftSubst′ (wf ⊢A) ⊢Δ ⊢A s) (⊢Δ ∙ ⊢σA))
  where ⊢σA = substitution ⊢A s ⊢Δ

subNeg (sigma ⊢A nA nB) s ⊢Δ =
  sigma ⊢σA (subNeg nA s ⊢Δ)
    (subNeg nB (liftSubst′ (wf ⊢A) ⊢Δ ⊢A s) (⊢Δ ∙ ⊢σA))
  where ⊢σA = substitution ⊢A s ⊢Δ

subNeg (conv n c) s ⊢Δ =
  conv (subNeg n s ⊢Δ) (substitutionEq c (substRefl s) ⊢Δ)

-- Negative types are closed under single substitutions.

subNeg1 : NegativeType (Γ ∙ A) B → Γ ⊢ t ∷ A → NegativeType Γ (B [ t ]₀)
subNeg1 n ⊢t = subNeg n (singleSubst ⊢t) (wfTerm ⊢t)

-- The first component of a negative Σ-type is negative if the
-- quantity is not 𝟘.

fstNeg :
  NegativeType Γ C →
  Γ ⊢ C ≡ Σˢ p , q ▷ A ▹ B →
  𝟘 ≢ p →
  NegativeType Γ A
fstNeg empty          c  _   = ⊥-elim (Empty≢Σⱼ c)
fstNeg (pi _ _)       c  _   = ⊥-elim (Π≢Σⱼ c)
fstNeg (sigma-𝟘 _ _)  c  𝟘≢p = let _ , _ , 𝟘≡p , _ = Σ-injectivity c in
                               ⊥-elim (𝟘≢p 𝟘≡p)
fstNeg (sigma _ nA _) c  _   = conv nA (proj₁ (Σ-injectivity c))
fstNeg (conv n c)     c′ 𝟘≢p = fstNeg n (trans c c′) 𝟘≢p

-- Any instance of the second component of a negative Σ-type is
-- negative.

sndNeg :
  NegativeType Γ C →
  Γ ⊢ C ≡ Σˢ p , q ▷ A ▹ B →
  Γ ⊢ t ∷ A →
  NegativeType Γ (B [ t ]₀)
sndNeg empty          c    = ⊥-elim (Empty≢Σⱼ c)
sndNeg (pi _ _)       c    = ⊥-elim (Π≢Σⱼ c)
sndNeg (sigma-𝟘 _ nB) c ⊢t =
  let (cA , cB , _ , _) = Σ-injectivity c in
  subNeg (conv nB cB) (singleSubst (conv ⊢t (sym cA))) (wfTerm ⊢t)
sndNeg (sigma _ _ nB) c ⊢t =
  let (cA , cB , _ , _) = Σ-injectivity c in
  subNeg (conv nB cB) (singleSubst (conv ⊢t (sym cA))) (wfTerm ⊢t)
sndNeg (conv n c) c′ = sndNeg n (trans c c′)

-- Any instance of the codomain of a negative Π-type is negative.

appNeg :
  NegativeType Γ C →
  Γ ⊢ C ≡ Π p , q ▷ A ▹ B →
  Γ ⊢ t ∷ A →
  NegativeType Γ (B [ t ]₀)
appNeg empty          c = ⊥-elim (Empty≢Πⱼ c)
appNeg (sigma-𝟘 _ _)  c = ⊥-elim (Π≢Σⱼ (sym c))
appNeg (sigma _ _ _)  c = ⊥-elim (Π≢Σⱼ (sym c))
appNeg (pi _ nB) c ⊢t =
  let (cA , cB , _ , _) = injectivity c in
  subNeg (conv nB cB) (singleSubst (conv ⊢t (sym cA))) (wfTerm ⊢t)
appNeg (conv n c) c′ = appNeg n (trans c c′)

-- The type ℕ is not negative.

¬negℕ : NegativeType Γ C → Γ ⊢ C ≡ ℕ → ⊥
¬negℕ empty         c  = ℕ≢Emptyⱼ (sym c)
¬negℕ (pi _ _)      c  = ℕ≢Π (sym c)
¬negℕ (sigma-𝟘 _ _) c  = ℕ≢Σ (sym c)
¬negℕ (sigma _ _ _) c  = ℕ≢Σ (sym c)
¬negℕ (conv n c)    c′ = ¬negℕ n (trans c c′)

-- Σʷ-types are not negative.

¬negΣʷ : NegativeType Γ C → Γ ⊢ C ≡ Σʷ p , q ▷ A ▹ B → ⊥
¬negΣʷ empty         c  = Empty≢Bⱼ BΣ! c
¬negΣʷ (pi _ _)      c  = Π≢Σⱼ c
¬negΣʷ (sigma-𝟘 _ _) c  = Σˢ≢Σʷⱼ c
¬negΣʷ (sigma _ _ _) c  = Σˢ≢Σʷⱼ c
¬negΣʷ (conv n c)    c′ = ¬negΣʷ n (trans c c′)

-- Unit types are not negative

¬negUnit : ∀ {s} → NegativeType Γ C → Γ ⊢ C ≡ Unit s l → ⊥
¬negUnit empty         c  = Empty≢Unitⱼ c
¬negUnit (pi _ _)      c  = Unit≢Πⱼ (sym c)
¬negUnit (sigma-𝟘 _ _) c  = Unit≢Σⱼ (sym c)
¬negUnit (sigma _ _ _) c  = Unit≢Σⱼ (sym c)
¬negUnit (conv n c)    c′ = ¬negUnit n (trans c c′)

opaque

  -- Identity types are not negative.

  ¬negId : NegativeType Γ A → ¬ Γ ⊢ A ≡ Id B t u
  ¬negId empty         = Id≢Empty ∘→ sym
  ¬negId (pi _ _)      = I.Id≢ΠΣ ∘→ sym
  ¬negId (sigma-𝟘 _ _) = I.Id≢ΠΣ ∘→ sym
  ¬negId (sigma _ _ _) = I.Id≢ΠΣ ∘→ sym
  ¬negId (conv n B≡A)  = ¬negId n ∘→ trans B≡A
