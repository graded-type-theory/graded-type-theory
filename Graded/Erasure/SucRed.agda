------------------------------------------------------------------------
-- Extended reduction relations allowing reduction under suc.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Graded.Erasure.SucRed
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Tools.Empty
open import Tools.Function
open import Tools.List using (List)
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Sum
open import Tools.Unit

open import Definition.Untyped M
open import Definition.Untyped.Whnf M type-variant
open import Definition.Typed R
open import Definition.Typed.Consequences.Consistency R
open import Definition.Typed.Properties R
open import Definition.Typed.Well-formed R

open import Graded.Erasure.Target as T
  using (Strictness; strict; non-strict)
open import Graded.Erasure.Target.Non-terminating
import Graded.Erasure.Target.Properties as TP


private
  variable
    m n : Nat
    Γ : Cons _ _
    ∇ : List (T.Term 0)
    t t′ u u₁ u₂ : Term n
    v v′ w w′ : T.Term n
    ρ : Wk _ _
    s : Strictness

------------------------------------------------------------------------
-- _⊢_⇒ˢ*_∷ℕ

-- Extended reduction relation for natural numbers.
-- Allows reduction under suc

infix 4 _⊢_⇒ˢ_∷ℕ

data _⊢_⇒ˢ_∷ℕ (Γ : Cons m n) : (t u : Term n) → Set a where
  whred : Γ ⊢ t ⇒ u ∷ ℕ → Γ ⊢ t ⇒ˢ u ∷ℕ
  sucred : Γ ⊢ t ⇒ˢ u ∷ℕ → Γ ⊢ suc t ⇒ˢ suc u ∷ℕ

-- Extended reduction relation closure for natural numbers.
-- Allows reduction under suc

infix 4 _⊢_⇒ˢ*_∷ℕ

data _⊢_⇒ˢ*_∷ℕ (Γ : Cons m n) : (t u : Term n) → Set a where
  id : Γ ⊢ t ∷ ℕ → Γ ⊢ t ⇒ˢ* t ∷ℕ
  _⇨ˢ_ : Γ ⊢ t ⇒ˢ t′ ∷ℕ → Γ ⊢ t′ ⇒ˢ* u ∷ℕ → Γ ⊢ t ⇒ˢ* u ∷ℕ

⇒ˢ*∷ℕ-trans : Γ ⊢ t ⇒ˢ* t′ ∷ℕ → Γ ⊢ t′ ⇒ˢ* u ∷ℕ → Γ ⊢ t ⇒ˢ* u ∷ℕ
⇒ˢ*∷ℕ-trans (id x) d′ = d′
⇒ˢ*∷ℕ-trans (x ⇨ˢ d) d′ = x ⇨ˢ ⇒ˢ*∷ℕ-trans d d′

whred* : Γ ⊢ t ⇒* u ∷ ℕ → Γ ⊢ t ⇒ˢ* u ∷ℕ
whred* (id x) = id x
whred* (x ⇨ d) = whred x ⇨ˢ whred* d

sucred* : Γ ⊢ t ⇒ˢ* u ∷ℕ → Γ ⊢ suc t ⇒ˢ* suc u ∷ℕ
sucred* (id x) = id (sucⱼ x)
sucred* (x ⇨ˢ d) = (sucred x) ⇨ˢ (sucred* d)

subsetTermˢ : Γ ⊢ t ⇒ˢ u ∷ℕ → Γ ⊢ t ≡ u ∷ ℕ
subsetTermˢ (whred x) = subsetTerm x
subsetTermˢ (sucred d) = suc-cong (subsetTermˢ d)

subset*Termˢ : Γ ⊢ t ⇒ˢ* u ∷ℕ → Γ ⊢ t ≡ u ∷ ℕ
subset*Termˢ (id x) = refl x
subset*Termˢ (x ⇨ˢ d) = trans (subsetTermˢ x) (subset*Termˢ d)

-- If t reduces to u according to _⊢_⇒ˢ_∷ℕ, and u is definitionally
-- equal to zero, then t reduces to u (given a certain assumption).

⇒ˢ∷ℕ≡zero→⇒ :
  ⦃ ok : No-equality-reflection or-empty Γ .vars ⦄ →
  Γ ⊢ t ⇒ˢ u ∷ℕ → Γ ⊢ u ≡ zero ∷ ℕ → Γ ⊢ t ⇒ u ∷ ℕ
⇒ˢ∷ℕ≡zero→⇒ (whred t⇒u) _        = t⇒u
⇒ˢ∷ℕ≡zero→⇒ (sucred _)  suc≡zero = ⊥-elim (zero≢suc (sym′ suc≡zero))

-- If t reduces to u according to _⊢_⇒ˢ*_∷ℕ, and u is definitionally
-- equal to zero, then t reduces to u (given a certain assumption).

⇒ˢ*∷ℕ≡zero→⇒* :
  ⦃ ok : No-equality-reflection or-empty Γ .vars ⦄ →
  Γ ⊢ t ⇒ˢ* u ∷ℕ → Γ ⊢ u ≡ zero ∷ ℕ → Γ ⊢ t ⇒* u ∷ ℕ
⇒ˢ*∷ℕ≡zero→⇒* (id ⊢t)       _   = id ⊢t
⇒ˢ*∷ℕ≡zero→⇒* (t⇒v ⇨ˢ v⇒*u) u≡0 =
  ⇒ˢ∷ℕ≡zero→⇒ t⇒v (trans (subset*Termˢ v⇒*u) u≡0) ⇨
  ⇒ˢ*∷ℕ≡zero→⇒* v⇒*u u≡0

-- If t reduces to zero according to _⊢_⇒ˢ_∷ℕ, then t reduces to zero
-- (given a certain assumption).

⇒ˢzero∷ℕ→⇒zero :
  ⦃ ok : No-equality-reflection or-empty Γ .vars ⦄ →
  Γ ⊢ t ⇒ˢ zero ∷ℕ → Γ ⊢ t ⇒ zero ∷ ℕ
⇒ˢzero∷ℕ→⇒zero t⇒ =
  ⇒ˢ∷ℕ≡zero→⇒ t⇒ (refl (zeroⱼ (wf (subsetTermˢ t⇒))))

-- If t reduces to zero according to _⊢_⇒ˢ*_∷ℕ, then t reduces to
-- zero (given a certain assumption).

⇒ˢ*zero∷ℕ→⇒*zero :
  ⦃ ok : No-equality-reflection or-empty Γ .vars ⦄ →
  Γ ⊢ t ⇒ˢ* zero ∷ℕ → Γ ⊢ t ⇒* zero ∷ ℕ
⇒ˢ*zero∷ℕ→⇒*zero t⇒ =
  ⇒ˢ*∷ℕ≡zero→⇒* t⇒ (refl (zeroⱼ (wf (subset*Termˢ t⇒))))

opaque

  -- If t reduces to u according to _⊢_⇒ˢ*_∷ℕ, then t reduces to
  -- either u or an application of suc according to _⊢_⇒*_∷_.

  ⇒ˢ*∷ℕ→⇒*⊎⇒*suc :
    Γ ⊢ t ⇒ˢ* u ∷ℕ → Γ ⊢ t ⇒* u ∷ ℕ ⊎ ∃ λ v → Γ ⊢ t ⇒* suc v ∷ ℕ
  ⇒ˢ*∷ℕ→⇒*⊎⇒*suc (id ⊢t)           = inj₁ (id ⊢t)
  ⇒ˢ*∷ℕ→⇒*⊎⇒*suc (sucred t⇒v ⇨ˢ _) =
    inj₂ (_ , id (sucⱼ (wf-⊢ (subsetTermˢ t⇒v) .proj₂ .proj₁)))
  ⇒ˢ*∷ℕ→⇒*⊎⇒*suc (whred t⇒v ⇨ˢ v⇒*u) =
    case ⇒ˢ*∷ℕ→⇒*⊎⇒*suc v⇒*u of λ where
      (inj₁ v⇒*u)           → inj₁ (t⇒v ⇨ v⇒*u)
      (inj₂ (_ , v⇒*suc-w)) → inj₂ (_ , t⇒v ⇨ v⇒*suc-w)

opaque

  -- Numerals do not reduce.

  numerals-do-not-reduce-⊢⇒ˢ∷ℕ : Numeral t → ¬ Γ ⊢ t ⇒ˢ u ∷ℕ
  numerals-do-not-reduce-⊢⇒ˢ∷ℕ zeroₙ (whred zero⇒) =
    whnfRedTerm zero⇒ zeroₙ
  numerals-do-not-reduce-⊢⇒ˢ∷ℕ (sucₙ t-n) (whred suc⇒) =
    whnfRedTerm suc⇒ sucₙ
  numerals-do-not-reduce-⊢⇒ˢ∷ℕ (sucₙ t-n) (sucred t⇒) =
    numerals-do-not-reduce-⊢⇒ˢ∷ℕ t-n t⇒

opaque

  -- The relation _⊢_⇒ˢ_∷ℕ is deterministic.

  deterministic-⊢⇒ˢ∷ℕ : Γ ⊢ t ⇒ˢ u₁ ∷ℕ → Γ ⊢ t ⇒ˢ u₂ ∷ℕ → u₁ PE.≡ u₂
  deterministic-⊢⇒ˢ∷ℕ (whred t⇒u₁) (whred t⇒u₂) =
    whrDetTerm t⇒u₁ t⇒u₂
  deterministic-⊢⇒ˢ∷ℕ (whred suc⇒) (sucred _) =
    ⊥-elim $ whnfRedTerm suc⇒ sucₙ
  deterministic-⊢⇒ˢ∷ℕ (sucred _) (whred suc⇒) =
    ⊥-elim $ whnfRedTerm suc⇒ sucₙ
  deterministic-⊢⇒ˢ∷ℕ (sucred t⇒u₁) (sucred t⇒u₂) =
    PE.cong suc $ deterministic-⊢⇒ˢ∷ℕ t⇒u₁ t⇒u₂

opaque

  -- The relation _⊢_⇒ˢ*_∷ℕ is deterministic when restricted to
  -- reduction to numerals.

  deterministic-⊢⇒ˢ*∷ℕ :
    Γ ⊢ t ⇒ˢ* u₁ ∷ℕ → Γ ⊢ t ⇒ˢ* u₂ ∷ℕ →
    Numeral u₁ → Numeral u₂ → u₁ PE.≡ u₂
  deterministic-⊢⇒ˢ*∷ℕ (id _) (id _) _ _ = PE.refl
  deterministic-⊢⇒ˢ*∷ℕ (id _) (t⇒ ⇨ˢ _) t-num _ =
    ⊥-elim $ numerals-do-not-reduce-⊢⇒ˢ∷ℕ t-num t⇒
  deterministic-⊢⇒ˢ*∷ℕ (t⇒ ⇨ˢ _) (id _) _ t-num =
    ⊥-elim $ numerals-do-not-reduce-⊢⇒ˢ∷ℕ t-num t⇒
  deterministic-⊢⇒ˢ*∷ℕ (t⇒u₁ ⇨ˢ u₁⇒*v₁) (t⇒u₂ ⇨ˢ u₂⇒*v₂) v₁-num v₂-num
    rewrite deterministic-⊢⇒ˢ∷ℕ t⇒u₁ t⇒u₂ =
    deterministic-⊢⇒ˢ*∷ℕ u₁⇒*v₁ u₂⇒*v₂ v₁-num v₂-num

------------------------------------------------------------------------
-- _⊢_⇒ˢ*_

-- Extended reduction relation for the target language
-- Allows reduction under suc

infix 4 _⊢_⇒ˢ_

data _⊢_⇒ˢ_ (∇ : List (T.Term 0)) : (_ _ : T.Term n) → Set where
  whred : ∇ T.⊢ v ⇒ w → ∇ ⊢ v ⇒ˢ w
  sucred : ∇ ⊢ v ⇒ˢ w → ∇ ⊢ T.suc v ⇒ˢ T.suc w

-- Extended reduction relation closure for the target language
-- Allows reduction under suc

infix 4 _⊢_⇒ˢ*_

data _⊢_⇒ˢ*_ (∇ : List (T.Term 0)) : (v w : T.Term n) → Set where
  refl : ∇ ⊢ v ⇒ˢ* v
  trans : ∇ ⊢ v ⇒ˢ v′ → ∇ ⊢ v′ ⇒ˢ* w → ∇ ⊢ v ⇒ˢ* w

⇒ˢ*-trans : ∇ ⊢ v ⇒ˢ* v′ → ∇ ⊢ v′ ⇒ˢ* w → ∇ ⊢ v ⇒ˢ* w
⇒ˢ*-trans refl d′ = d′
⇒ˢ*-trans (trans d d₁) d′ = trans d (⇒ˢ*-trans d₁ d′)

whred*′ : ∇ T.⊢ v ⇒* w → ∇ ⊢ v ⇒ˢ* w
whred*′ T.refl = refl
whred*′ (T.trans x d) = trans (whred x) (whred*′ d)

sucred*′ : ∇ ⊢ v ⇒ˢ* w → ∇ ⊢ T.suc v ⇒ˢ* T.suc w
sucred*′ refl = refl
sucred*′ (trans x d) = trans (sucred x) (sucred*′ d)

-- Is-suc v is inhabited if v is of the form "T.suc something".

Is-suc : T.Term n → Set
Is-suc = λ where
  (T.suc _) → ⊤
  _         → ⊥

-- A view of a term as either "T.suc something" or not
-- "T.suc something".

data Suc-view : T.Term n → Set where
  is-suc     : Suc-view (T.suc v)
  not-is-suc : ¬ Is-suc v → Suc-view v

-- The view is total.

suc-view : (v : T.Term n) → Suc-view v
suc-view = λ where
  (T.suc _)        → is-suc
  (T.var _)        → not-is-suc (λ ())
  (T.defn _)       → not-is-suc (λ ())
  (T.lam _)        → not-is-suc (λ ())
  (_ T.∘⟨ _ ⟩ _)   → not-is-suc (λ ())
  (T.prod _ _)     → not-is-suc (λ ())
  (T.fst _)        → not-is-suc (λ ())
  (T.snd _)        → not-is-suc (λ ())
  (T.prodrec _ _)  → not-is-suc (λ ())
  T.zero           → not-is-suc (λ ())
  (T.natrec _ _ _) → not-is-suc (λ ())
  T.star           → not-is-suc (λ ())
  (T.unitrec _ _)  → not-is-suc (λ ())
  T.↯              → not-is-suc (λ ())

-- If v reduces to w and v is of the form "T.suc something", then w is
-- of the form "T.suc something".

suc⇒*suc : ∇ T.⊢ v ⇒* w → Is-suc v → Is-suc w
suc⇒*suc         T.refl         is-suc-v = is-suc-v
suc⇒*suc {v = v} (T.trans v⇒ _) is-suc-v =
  case suc-view v of λ where
    is-suc                    → case v⇒ of λ ()
    (not-is-suc not-is-suc-v) → ⊥-elim (not-is-suc-v is-suc-v)

-- If v reduces to w according to _⊢_⇒ˢ_, and w is not of the form
-- "T.suc something", then v reduces to w.

⇒ˢ≢suc→⇒ : ∇ ⊢ v ⇒ˢ w → ¬ Is-suc w → ∇ T.⊢ v ⇒ w
⇒ˢ≢suc→⇒ (whred v⇒w) _       = v⇒w
⇒ˢ≢suc→⇒ (sucred _)  not-suc = ⊥-elim (not-suc _)

-- If v reduces to w according to _⊢_⇒ˢ*_, and w is not of the form
-- "T.suc something", then v reduces to w.

⇒ˢ*≢suc→⇒* : ∇ ⊢ v ⇒ˢ* w → ¬ Is-suc w → ∇ T.⊢ v ⇒* w
⇒ˢ*≢suc→⇒* refl               _       = T.refl
⇒ˢ*≢suc→⇒* (trans v⇒v′ v′⇒*w) not-suc =
  T.trans (⇒ˢ≢suc→⇒ v⇒v′ (not-suc ∘→ suc⇒*suc v′⇒*w′)) v′⇒*w′
  where
  v′⇒*w′ = ⇒ˢ*≢suc→⇒* v′⇒*w not-suc

-- If v reduces to T.zero according to _⊢_⇒ˢ_, then v reduces to
-- T.zero.

⇒ˢzero→⇒zero : ∇ ⊢ v ⇒ˢ T.zero → ∇ T.⊢ v ⇒ T.zero
⇒ˢzero→⇒zero = flip ⇒ˢ≢suc→⇒ (λ ())

-- If v reduces to T.zero according to _⊢_⇒ˢ*_, then v reduces to
-- T.zero.

⇒ˢ*zero→⇒*zero : ∇ ⊢ v ⇒ˢ* T.zero → ∇ T.⊢ v ⇒* T.zero
⇒ˢ*zero→⇒*zero = flip ⇒ˢ*≢suc→⇒* (λ ())

-- If v reduces to T.suc w according to _⊢_⇒ˢ_, then v reduces to
-- T.suc something.

⇒ˢsuc→⇒*suc : ∇ ⊢ v ⇒ˢ T.suc w → ∃ λ w → ∇ T.⊢ v ⇒* T.suc w
⇒ˢsuc→⇒*suc (whred v⇒)  = _ , T.trans v⇒ T.refl
⇒ˢsuc→⇒*suc (sucred v⇒) = _ , T.refl

-- If v reduces to T.suc w according to _⊢_⇒ˢ*_, then v reduces to
-- T.suc something.

⇒ˢ*suc→⇒*suc : ∇ ⊢ v ⇒ˢ* T.suc w → ∃ λ w → ∇ T.⊢ v ⇒* T.suc w
⇒ˢ*suc→⇒*suc = λ where
  refl →
    _ , T.refl
  (trans {v′ = v′} v⇒v′ v′⇒*suc) → case suc-view v′ of λ where
    is-suc               → ⇒ˢsuc→⇒*suc v⇒v′
    (not-is-suc not-suc) →
      case ⇒ˢ*suc→⇒*suc v′⇒*suc of λ {
        (_ , v′⇒*suc) →
      _ , T.trans (⇒ˢ≢suc→⇒ v⇒v′ not-suc) v′⇒*suc }

opaque

  -- If v reduces to w according to _⊢_⇒ˢ*_, then v reduces to either w
  -- or an application of T.suc according to T._⊢_⇒*_.

  ⇒ˢ*→⇒*⊎⇒*suc :
    ∇ ⊢ v ⇒ˢ* w → ∇ T.⊢ v ⇒* w ⊎ ∃ λ w′ → ∇ T.⊢ v ⇒* T.suc w′
  ⇒ˢ*→⇒*⊎⇒*suc refl                      = inj₁ T.refl
  ⇒ˢ*→⇒*⊎⇒*suc (trans (sucred _) _)      = inj₂ (_ , T.refl)
  ⇒ˢ*→⇒*⊎⇒*suc (trans (whred v⇒v′) v′⇒w) =
    case ⇒ˢ*→⇒*⊎⇒*suc v′⇒w of λ where
      (inj₁ v′⇒w)         → inj₁ (T.trans v⇒v′ v′⇒w)
      (inj₂ (_ , v′⇒suc)) → inj₂ (_ , T.trans v⇒v′ v′⇒suc)

opaque

  -- A weakening lemma for extended reduction.

  wk-⇒ˢ : ∇ ⊢ v ⇒ˢ w → ∇ ⊢ T.wk ρ v ⇒ˢ T.wk ρ w
  wk-⇒ˢ = λ where
    (whred d)  → whred (TP.wk-⇒ d)
    (sucred d) → sucred (wk-⇒ˢ d)

opaque

  -- A weakening lemma for extended reduction.

  wk-⇒ˢ* : ∇ ⊢ v ⇒ˢ* w → ∇ ⊢ T.wk ρ v ⇒ˢ* T.wk ρ w
  wk-⇒ˢ* = λ where
    refl          → refl
    (trans d₁ d₂) → trans (wk-⇒ˢ d₁) (wk-⇒ˢ* d₂)

opaque

  -- A strengthening lemma for extended reduction.

  strengthen-⇒ˢ :
    ∇ ⊢ T.wk ρ v ⇒ˢ w → ∃ λ w′ → T.wk ρ w′ PE.≡ w × ∇ ⊢ v ⇒ˢ w′
  strengthen-⇒ˢ = flip lemma PE.refl
    where
    lemma :
      ∇ ⊢ v ⇒ˢ w → T.wk ρ v′ PE.≡ v →
      ∃ λ w′ → T.wk ρ w′ PE.≡ w × ∇ ⊢ v′ ⇒ˢ w′
    lemma = λ where
      (whred d) PE.refl →
        case TP.strengthen-⇒ d of λ {
          (_ , PE.refl , d) →
        _ , PE.refl , whred d }
      (sucred d) eq →
        case TP.inv-wk-suc eq of λ {
          (_ , PE.refl , PE.refl) →
        case strengthen-⇒ˢ d of λ {
          (_ , PE.refl , d) →
        _ , PE.refl , sucred d }}

opaque

  -- A strengthening lemma for extended reduction.

  strengthen-⇒ˢ* :
    ∇ ⊢ T.wk ρ v ⇒ˢ* w → ∃ λ w′ → T.wk ρ w′ PE.≡ w × ∇ ⊢ v ⇒ˢ* w′
  strengthen-⇒ˢ* = λ where
    refl →
      _ , PE.refl , refl
    (trans d₁ d₂) →
      case strengthen-⇒ˢ d₁ of λ {
        (_ , PE.refl , d₁) →
      case strengthen-⇒ˢ* d₂ of λ {
        (_ , PE.refl , d₂) →
      _ , PE.refl , trans d₁ d₂ }}

opaque

  -- If T.wk ρ v reduces to a numeral, then v reduces to the same
  -- numeral.

  strengthen-⇒ˢ*-sucⁿ : ∇ ⊢ T.wk ρ v ⇒ˢ* T.sucⁿ n → ∇ ⊢ v ⇒ˢ* T.sucⁿ n
  strengthen-⇒ˢ*-sucⁿ d =
    case strengthen-⇒ˢ* d of λ {
      (_ , eq , d) →
    case TP.inv-wk-sucⁿ eq of λ {
      PE.refl →
    d }}

------------------------------------------------------------------------
-- _⊢_⇒ˢ⟨_⟩*_

-- The extended relation _⊢_⇒ˢ*_ is only used when non-strict
-- applications are used, otherwise T._⊢_⇒*_ is used.

infix 4 _⊢_⇒ˢ⟨_⟩*_

_⊢_⇒ˢ⟨_⟩*_ : List (T.Term 0) → T.Term n → Strictness → T.Term n → Set
∇ ⊢ v ⇒ˢ⟨ non-strict ⟩* w = ∇ ⊢ v ⇒ˢ* w
∇ ⊢ v ⇒ˢ⟨ strict     ⟩* w = ∇ T.⊢ v ⇒* w

opaque

  -- The relation _⊢_⇒ˢ⟨_⟩*_ is "reflexive".

  refl-⇒ˢ⟨⟩* : ∇ ⊢ v ⇒ˢ⟨ s ⟩* v
  refl-⇒ˢ⟨⟩* {s = non-strict} = refl
  refl-⇒ˢ⟨⟩* {s = strict}     = T.refl

opaque

  -- The relation T._⊢_⇒*_ is contained in _⊢_⇒ˢ⟨ s ⟩*_.

  ⇒*→⇒ˢ⟨⟩* : ∇ T.⊢ v ⇒* w → ∇ ⊢ v ⇒ˢ⟨ s ⟩* w
  ⇒*→⇒ˢ⟨⟩* {s = non-strict} = whred*′
  ⇒*→⇒ˢ⟨⟩* {s = strict}     = idᶠ

opaque
  unfolding loop

  -- The term loop s does not reduce to a value.

  ¬loop⇒ˢ* : T.Value v → ¬ ∇ ⊢ loop s ⇒ˢ⟨ s ⟩* v
  ¬loop⇒ˢ* {s = strict} =
    ¬loop⇒*
  ¬loop⇒ˢ* {s = non-strict} = ¬loop⇒ˢ*′
    where
    ¬loop⇒ˢ*′ : T.Value v → ¬ ∇ ⊢ loop non-strict ⇒ˢ* v
    ¬loop⇒ˢ*′ {∇} loop-value refl =
      ¬loop⇒* {∇ = ∇} loop-value T.refl
    ¬loop⇒ˢ*′ v-value (trans (whred loop⇒) ⇒*v)
      rewrite TP.redDet _ loop⇒ loop⇒loop =
      ¬loop⇒ˢ*′ v-value ⇒*v

opaque

  -- A weakening lemma for _⊢_⇒ˢ⟨_⟩*_.

  wk-⇒ˢ⟨⟩* : ∇ ⊢ v ⇒ˢ⟨ s ⟩* w → ∇ ⊢ T.wk ρ v ⇒ˢ⟨ s ⟩* T.wk ρ w
  wk-⇒ˢ⟨⟩* {s = non-strict} = wk-⇒ˢ*
  wk-⇒ˢ⟨⟩* {s = strict}     = TP.wk-⇒*

opaque

  -- A strengthening lemma for _⊢_⇒ˢ⟨_⟩*_.

  strengthen-⇒ˢ⟨⟩* :
    ∇ ⊢ T.wk ρ v ⇒ˢ⟨ s ⟩* w →
    ∃ λ w′ → T.wk ρ w′ PE.≡ w × ∇ ⊢ v ⇒ˢ⟨ s ⟩* w′
  strengthen-⇒ˢ⟨⟩* {s = non-strict} = strengthen-⇒ˢ*
  strengthen-⇒ˢ⟨⟩* {s = strict}     = TP.strengthen-⇒*

opaque

  -- If T.wk ρ v reduces to a numeral, then v reduces to the same
  -- numeral.

  strengthen-⇒ˢ⟨⟩*-sucⁿ :
    ∇ ⊢ T.wk ρ v ⇒ˢ⟨ s ⟩* T.sucⁿ n → ∇ ⊢ v ⇒ˢ⟨ s ⟩* T.sucⁿ n
  strengthen-⇒ˢ⟨⟩*-sucⁿ {s = strict}     = TP.strengthen-⇒*-sucⁿ
  strengthen-⇒ˢ⟨⟩*-sucⁿ {s = non-strict} = strengthen-⇒ˢ*-sucⁿ
