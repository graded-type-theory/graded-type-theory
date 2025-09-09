------------------------------------------------------------------------
-- Properties for the reduction relation of the target language.
------------------------------------------------------------------------

module Graded.Erasure.Target.Properties.Reduction where

open import Graded.Erasure.Target

open import Tools.Empty
open import Tools.Function
open import Tools.List
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Sum

private
  variable
    α k n : Nat
    t t′ u u′ v : Term n
    ∇ ∇′ : List (Term _)
    s : Strictness

-- Reduction properties

-- Concatenation of reduction closure

red*concat : ∇ ⊢ t ⇒* t′ → ∇ ⊢ t′ ⇒* u → ∇ ⊢ t ⇒* u
red*concat refl t′⇒*u = t′⇒*u
red*concat (trans x t⇒*t′) t′⇒*u = trans x (red*concat t⇒*t′ t′⇒*u)

-- Closure of substitution reductions

app-subst* : ∇ ⊢ t ⇒* t′ → ∇ ⊢ t ∘⟨ s ⟩ u ⇒* t′ ∘⟨ s ⟩ u
app-subst* refl = refl
app-subst* (trans x t⇒*t′) = trans (app-subst x) (app-subst* t⇒*t′)

app-subst*-arg :
  Value t → ∇ ⊢ u ⇒* u′ → ∇ ⊢ t ∘⟨ strict ⟩ u ⇒* t ∘⟨ strict ⟩ u′
app-subst*-arg _   refl                = refl
app-subst*-arg val (trans u⇒u′ u′⇒*u″) =
  trans (app-subst-arg val u⇒u′) (app-subst*-arg val u′⇒*u″)

fst-subst* : ∇ ⊢ t ⇒* t′ → ∇ ⊢ fst t ⇒* fst t′
fst-subst* refl = refl
fst-subst* (trans x t⇒*t′) = trans (fst-subst x) (fst-subst* t⇒*t′)

snd-subst* : ∇ ⊢ t ⇒* t′ → ∇ ⊢ snd t ⇒* snd t′
snd-subst* refl = refl
snd-subst* (trans x t⇒*t′) = trans (snd-subst x) (snd-subst* t⇒*t′)

natrec-subst* :
  ∀ {z s} → ∇ ⊢ t ⇒* t′ → ∇ ⊢ natrec z s t ⇒* natrec z s t′
natrec-subst* refl = refl
natrec-subst* (trans x t⇒t′) = trans (natrec-subst x) (natrec-subst* t⇒t′)

prodrec-subst* : ∇ ⊢ t ⇒* t′ → ∇ ⊢ prodrec t u ⇒* prodrec t′ u
prodrec-subst* refl = refl
prodrec-subst* (trans x t⇒t′) = trans (prodrec-subst x) (prodrec-subst* t⇒t′)

unitrec-subst* : ∇ ⊢ t ⇒* t′ → ∇ ⊢ unitrec t u ⇒* unitrec t′ u
unitrec-subst* refl = refl
unitrec-subst* (trans x d) = trans (unitrec-subst x) (unitrec-subst* d)

-- Values do not reduce.

opaque

  Value→¬⇒ : Value t → ¬ ∇ ⊢ t ⇒ u
  Value→¬⇒ lam  ()
  Value→¬⇒ prod ()
  Value→¬⇒ zero ()
  Value→¬⇒ suc  ()
  Value→¬⇒ star ()
  Value→¬⇒ ↯    ()

opaque

  -- If t ∘⟨ s ⟩ u reduces to a value, then t reduces to a value.

  ∘⇒Value→⇒Value :
    Value v → ∇ ⊢ t ∘⟨ s ⟩ u ⇒* v → ∃ λ v′ → Value v′ × ∇ ⊢ t ⇒* v′
  ∘⇒Value→⇒Value ()      refl
  ∘⇒Value→⇒Value v-value (trans (app-subst t⇒t′) t′u⇒v) =
    let _ , v′-value , t′⇒v′ = ∘⇒Value→⇒Value v-value t′u⇒v in
    _ , v′-value , trans t⇒t′ t′⇒v′
  ∘⇒Value→⇒Value _ (trans (app-subst-arg t-value _) _) =
    _ , t-value , refl
  ∘⇒Value→⇒Value _ (trans (β-red _) _) =
    _ , lam , refl

opaque

  -- List indexing is deterministic.

  ↦∈-deterministic : α ↦ t ∈ ∇ → α ↦ u ∈ ∇ → t PE.≡ u
  ↦∈-deterministic here       here       = PE.refl
  ↦∈-deterministic (there t∈) (there u∈) = ↦∈-deterministic t∈ u∈

opaque

  -- If α points to t in ∇, then α points to t in ∇ ++ ∇′.

  ↦∈++ : α ↦ t ∈ ∇ → α ↦ t ∈ (∇ ++ ∇′)
  ↦∈++ here        = here
  ↦∈++ (there α↦t) = there (↦∈++ α↦t)

opaque

  -- The number length ∇ points to t in ∇ ++ t ∷ ∇′.

  length↦∈++∷ : length ∇ ↦ t ∈ (∇ ++ t ∷ ∇′)
  length↦∈++∷ {∇ = []}    = here
  length↦∈++∷ {∇ = _ ∷ _} = there length↦∈++∷

opaque

  -- Reduction is deterministic.

  redDet : (u : Term n) → ∇ ⊢ u ⇒ t → ∇ ⊢ u ⇒ t′ → t PE.≡ t′
  redDet _ = λ where
    (δ-red α↦t) → λ where
      (δ-red α↦t′) → PE.cong (wk _) $ ↦∈-deterministic α↦t α↦t′
    (app-subst p) → λ where
      (app-subst q)       → PE.cong (_∘⟨ _ ⟩ _) $ redDet _ p q
      (app-subst-arg v _) → ⊥-elim $ Value→¬⇒ v p
      (β-red _)           → case p of λ ()
    (app-subst-arg v p) → λ where
      (app-subst q)       → ⊥-elim $ Value→¬⇒ v q
      (app-subst-arg _ q) → PE.cong (_ ∘⟨ _ ⟩_) $ redDet _ p q
      (β-red v)           → ⊥-elim $ Value→¬⇒ v p
    (β-red v) → λ where
      (app-subst ())
      (app-subst-arg _ q) → ⊥-elim $ Value→¬⇒ v q
      (β-red _)           → PE.refl
    (fst-subst p) → λ where
      (fst-subst q) → PE.cong fst $ redDet _ p q
      Σ-β₁          → case p of λ ()
    (snd-subst p) → λ where
      (snd-subst q) → PE.cong snd $ redDet _ p q
      Σ-β₂          → case p of λ ()
    Σ-β₁ → λ where
      (fst-subst ())
      Σ-β₁           → PE.refl
    Σ-β₂ → λ where
      (snd-subst ())
      Σ-β₂           → PE.refl
    (prodrec-subst p) → λ where
      (prodrec-subst q) → PE.cong (flip prodrec _) $ redDet _ p q
      prodrec-β         → case p of λ ()
    prodrec-β → λ where
      (prodrec-subst ())
      prodrec-β          → PE.refl
    (natrec-subst p) → λ where
      (natrec-subst q) → PE.cong (natrec _ _) $ redDet _ p q
      natrec-zero      → case p of λ ()
      natrec-suc       → case p of λ ()
    natrec-zero → λ where
      (natrec-subst ())
      natrec-zero       → PE.refl
    natrec-suc → λ where
      (natrec-subst ())
      natrec-suc        → PE.refl
    (unitrec-subst p) → λ where
      (unitrec-subst q) → PE.cong (flip unitrec _) $ redDet _ p q
      unitrec-β         → case p of λ ()
    unitrec-β → λ where
      (unitrec-subst ())
      unitrec-β          → PE.refl

-- Reduction closure is deterministic
-- (there is only one reduction path)
-- If a ⇒* b and a ⇒* c then b ⇒* c or c ⇒* b

red*Det : ∇ ⊢ u ⇒* t → ∇ ⊢ u ⇒* t′ → (∇ ⊢ t ⇒* t′) ⊎ (∇ ⊢ t′ ⇒* t)
red*Det refl refl = inj₁ refl
red*Det refl (trans x u⇒t′) = inj₁ (trans x u⇒t′)
red*Det (trans x u⇒t) refl = inj₂ (trans x u⇒t)
red*Det {u = u} (trans x u⇒t) (trans x₁ u⇒t′)
  rewrite redDet u x x₁ = red*Det u⇒t u⇒t′

-- Non-reducible terms

↯-noRed : ∇ ⊢ ↯ ⇒* t → t PE.≡ ↯
↯-noRed refl         = PE.refl
↯-noRed (trans () _)

zero-noRed : ∇ ⊢ zero ⇒* t → t PE.≡ zero
zero-noRed refl         = PE.refl
zero-noRed (trans () _)

suc-noRed : ∇ ⊢ suc t ⇒* t′ → t′ PE.≡ suc t
suc-noRed refl         = PE.refl
suc-noRed (trans () _)

prod-noRed : ∇ ⊢ prod t t′ ⇒* u → u PE.≡ prod t t′
prod-noRed refl         = PE.refl
prod-noRed (trans () _)

star-noRed : ∇ ⊢ star ⇒* t → t PE.≡ star
star-noRed refl         = PE.refl
star-noRed (trans () _)

opaque

  Value→⇒*→≡ : Value t → ∇ ⊢ t ⇒* u → u PE.≡ t
  Value→⇒*→≡ = λ where
    lam  refl          → PE.refl
    prod refl          → PE.refl
    zero refl          → PE.refl
    suc  refl          → PE.refl
    star refl          → PE.refl
    ↯    refl          → PE.refl
    t-v  (trans t⇒u _) → ⊥-elim $ Value→¬⇒ t-v t⇒u

opaque

  -- If t is a value, then Value⟨ s ⟩ t holds.

  Value→Value⟨⟩ : Value t → Value⟨ s ⟩ t
  Value→Value⟨⟩ {s = strict}     v = v
  Value→Value⟨⟩ {s = non-strict} _ = _

opaque

  -- Numerals are values.

  Numeral→Value : Numeral t → Value t
  Numeral→Value zero    = zero
  Numeral→Value (suc _) = suc

opaque

  -- The term sucᵏ k is a value.

  Value-sucᵏ : Value (sucᵏ {n = n} k)
  Value-sucᵏ {k = 0}    = zero
  Value-sucᵏ {k = 1+ _} = suc
