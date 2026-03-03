------------------------------------------------------------------------
-- Non-empty natural number intervals
------------------------------------------------------------------------

module Graded.Modality.Instances.Set.Interval where

import Tools.Algebra
open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Nat as N using (Nat)
open import Tools.Product as Σ
open import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Sum as ⊎ using (_⊎_; inj₁; inj₂)

import Graded.Modality
import Graded.Modality.Instances.LowerBounded as LowerBounded
open import Graded.Modality.Instances.Set.Non-empty
  using (Is-non-empty-set-[])

private variable
  a     : Level
  A S   : Set _
  P Q   : A → Set _
  xs ys : S
  m n   : Nat

------------------------------------------------------------------------
-- Interval closure

-- The interval closure Closure P of a natural number predicate P
-- holds for numbers n such that P holds for some numbers l and m such
-- that l ≤ n ≤ m.

Closure : (Nat → Set a) → Nat → Set a
Closure P n =
  ∃₂ λ l m → l N.≤ n × n N.≤ m × P l × P m

-- The closure of P contains P.

included : P n → Closure P n
included p = _ , _ , N.≤-refl , N.≤-refl , p , p

-- The closure of P is closed.

closed : Closure (Closure P) n → Closure P n
closed
  {n = n}
  ( l , m , l≤n , n≤m
  , (l₁ , m₁ , l₁≤l , l≤m₁ , p-l₁ , p-m₁)
  , (l₂ , m₂ , l₂≤m , m≤m₂ , p-l₂ , p-m₂)
  ) =
    l₁ , m₂
  , (begin
       l₁  ≤⟨ l₁≤l ⟩
       l   ≤⟨ l≤n ⟩
       n   ∎)
  , (begin
       n   ≤⟨ n≤m ⟩
       m   ≤⟨ m≤m₂ ⟩
       m₂  ∎)
  , p-l₁ , p-m₂
  where
  open N.≤-Reasoning

-- A variant of the previous lemma.

Closure-Closure⇔ : Closure (Closure P) n ⇔ Closure P n
Closure-Closure⇔ = closed , included

-- If P holds for at most one number, then the closure of P is P
-- (pointwise, up to _⇔_).

Closure-at-most-one :
  (∀ {m n} → P m → P n → m ≡ n) → Closure P n ⇔ P n
Closure-at-most-one {P = P} {n = n} hyp =
    (λ (l , m , l≤n , n≤m , p-l , p-m) →
       flip (subst P) p-l $
       N.≤-antisym
         l≤n
         (begin
            n  ≤⟨ n≤m ⟩
            m  ≡⟨ hyp p-m p-l ⟩
            l  ∎))
  , included
  where
  open N.≤-Reasoning

-- A preservation lemma.

Closure-cong-→ :
  (∀ n → P n → Q n) → Closure P n → Closure Q n
Closure-cong-→ P→Q =
  Σ.map idᶠ $ Σ.map idᶠ $ Σ.map idᶠ $ Σ.map idᶠ $
  Σ.map (P→Q _) (P→Q _)

-- Another preservation lemma.

Closure-cong-⇔ :
  (∀ n → P n ⇔ Q n) → Closure P n ⇔ Closure Q n
Closure-cong-⇔ P⇔Q =
  Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ →
  P⇔Q _ ×-cong-⇔ P⇔Q _

-- A simplification lemma.

Closure-⊎ˡ :
  Closure (λ n → Closure P n ⊎ Q n) n ⇔
  Closure (λ n → P n ⊎ Q n) n
Closure-⊎ˡ {P = P} {Q = Q} {n = n} =
    (λ where
       (_ , _ , l≤n , n≤m ,
        inj₁ (l₁ , _ , l₁≤l , _ , p-l₁ , _) ,
        inj₁ (_ , m₂ , _ , m≤m₂ , _ , p-m₂)) →
           l₁ , m₂
         , N.≤-trans l₁≤l l≤n
         , N.≤-trans n≤m m≤m₂
         , inj₁ p-l₁ , inj₁ p-m₂
       (_ , m , l≤n , n≤m ,
        inj₁ (l₁ , _ , l₁≤l , _ , p-l₁ , _) ,
        inj₂ q-m) →
           l₁ , m
         , N.≤-trans l₁≤l l≤n
         , n≤m
         , inj₁ p-l₁ , inj₂ q-m
       (l , _ , l≤n , n≤m ,
        inj₂ q-l ,
        inj₁ (_ , m₂ , _ , m≤m₂ , _ , p-m₂)) →
           l , m₂
         , l≤n
         , N.≤-trans n≤m m≤m₂
         , inj₂ q-l , inj₁ p-m₂
       (l , m , l≤n , n≤m ,
        inj₂ q-l ,
        inj₂ q-m) →
           l , m , l≤n , n≤m , inj₂ q-l , inj₂ q-m)
  , (Closure-cong-→ λ _ → ⊎.map included idᶠ)

-- Another simplification lemma.

Closure-⊎ʳ :
  Closure (λ n → P n ⊎ Closure Q n) n ⇔
  Closure (λ n → P n ⊎ Q n) n
Closure-⊎ʳ {P = P} {Q = Q} {n = n} =
  Closure (λ n → P n ⊎ Closure Q n) n  ⇔⟨ (Closure-cong-⇔ λ _ → ⊎-comm-⇔) ⟩
  Closure (λ n → Closure Q n ⊎ P n) n  ⇔⟨ Closure-⊎ˡ ⟩
  Closure (λ n → Q n ⊎ P n) n          ⇔⟨ (Closure-cong-⇔ λ _ → ⊎-comm-⇔) ⟩
  Closure (λ n → P n ⊎ Q n) n          □⇔

-- Yet another simplification lemma.

Closure-⊎ :
  Closure (λ n → Closure P n ⊎ Closure Q n) n ⇔
  Closure (λ n → P n ⊎ Q n) n
Closure-⊎ {P = P} {Q = Q} {n = n} =
  Closure (λ n → Closure P n ⊎ Closure Q n) n  ⇔⟨ Closure-⊎ˡ ⟩
  Closure (λ n → P n ⊎ Closure Q n) n          ⇔⟨ Closure-⊎ʳ ⟩
  Closure (λ n → P n ⊎ Q n) n                  □⇔

-- A specification of non-empty natural number intervals with
-- singleton, union, addition, multiplication, a set that contains all
-- natural numbers, and decidable equality with the singleton set that
-- only contains 0.
--
-- For an implementation, see
-- Graded.Modality.Instances.Set.Interval.Implementation.

record Is-non-empty-interval (S : Set a) : Set (lsuc (lsuc a)) where
  no-eta-equality

  field
    -- Is-non-empty-interval S implies Is-non-empty-set-[] S.
    is-non-empty-set-[] : Is-non-empty-set-[] S

  open Is-non-empty-set-[] is-non-empty-set-[] public

  infixr 45 _·_
  infixr 40 _+_
  infixr 35 _∪_

  field
    -- The sets are intervals.
    interval : Closure (_∈ xs) n → n ∈ xs

    -- Union.
    _∪_ : S → S → S
    ∈∪⇔ : n ∈ xs ∪ ys ⇔ Closure (λ n → n ∈ xs ⊎ n ∈ ys) n

    -- Addition.
    _+_ : S → S → S
    ∈+⇔ :
      n ∈ xs + ys ⇔
      Closure (λ n → ∃₂ λ l m → l N.+ m ≡ n × l ∈ xs × m ∈ ys) n

    -- Multiplication.
    _·_ : S → S → S
    ∈·⇔ :
      n ∈ xs · ys ⇔
      Closure (λ n → ∃₂ λ l m → l N.* m ≡ n × l ∈ xs × m ∈ ys) n

    -- A set that contains all natural numbers.
    ℕ  : S
    ∈ℕ : n ∈ ℕ

    -- Equality with 𝟘 is decidable (modulo an Ext assumption for the
    -- "yes" case).
    is-𝟘? : ∀ xs → (Ext → xs ≡ 𝟘) ⊎ xs ≢ 𝟘

  ----------------------------------------------------------------------
  -- A lemma related to Closure

  -- Closure (_∈ xs) n is logically equivalent to n ∈ xs.

  Closure⇔ : Closure (_∈ xs) n ⇔ n ∈ xs
  Closure⇔ = interval , included

  ----------------------------------------------------------------------
  -- The relation _≤_

  -- An ordering relation.

  infix 10 _≤_

  _≤_ : S → S → Set a
  xs ≤ ys = xs ≡ xs ∪ ys

  private

    -- A lemma used in the proofs of ≤→ and ≤⇔.

    ≤⇔-lemma : (∀ n → n ∈ xs ⇔ n ∈ xs ∪ ys) ⇔ (∀ n → n ∈ ys → n ∈ xs)
    ≤⇔-lemma {xs = xs} {ys = ys} =
      (∀ n → n ∈ xs ⇔ n ∈ xs ∪ ys)         ⇔⟨ (Π-cong-⇔ λ _ →
                                                 proj₂
                                               , (∈∪⇔ .proj₂ ∘→ included ∘→ inj₁ ,_)) ⟩

      (∀ n → n ∈ xs ∪ ys → n ∈ xs)         ⇔⟨ (_∘→ ∈∪⇔ .proj₂ ∘→ included ∘→ inj₂) ∘→_
                                            , (λ hyp n →
        n ∈ xs ∪ ys                              ⇔⟨ ∈∪⇔ ⟩→
        Closure (λ n → n ∈ xs ⊎ n ∈ ys) n        →⟨ (Closure-cong-→ λ where
                                                       _ (inj₁ ∈xs) → ∈xs
                                                       _ (inj₂ ∈ys) → hyp _ ∈ys) ⟩
        Closure (_∈ xs) n                        ⇔⟨ Closure⇔ ⟩→
        n ∈ xs                                   □)
                                            ⟩

      (∀ n → n ∈ ys → n ∈ xs)              □⇔

  -- If xs ≤ ys, then every member of ys is also a member of xs.

  ≤→ : xs ≤ ys → (∀ n → n ∈ ys → n ∈ xs)
  ≤→ {xs = xs} {ys = ys} =
    xs ≤ ys                       ⇔⟨ id⇔ ⟩→
    xs ≡ xs ∪ ys                  →⟨ ≡→ ⟩
    (∀ n → n ∈ xs ⇔ n ∈ xs ∪ ys)  ⇔⟨ ≤⇔-lemma ⟩→
    (∀ n → n ∈ ys → n ∈ xs)       □

  -- The inequality xs ≤ ys holds if and only if every member of ys is
  -- also a member of xs (assuming that Ext is inhabited).

  ≤⇔ : Ext → xs ≤ ys ⇔ (∀ n → n ∈ ys → n ∈ xs)
  ≤⇔ {xs = xs} {ys = ys} ext =
    xs ≤ ys                       ⇔⟨ id⇔ ⟩
    xs ≡ xs ∪ ys                  ⇔⟨ ≡⇔ ext ⟩
    (∀ n → n ∈ xs ⇔ n ∈ xs ∪ ys)  ⇔⟨ ≤⇔-lemma ⟩
    (∀ n → n ∈ ys → n ∈ xs)       □⇔

  ----------------------------------------------------------------------
  -- The relation In

  -- Below _≤_ _∙_ xs ys n means that there are numbers l ∈ xs and
  -- m ∈ xs such that (l ∙ m) ≤ n holds: some combination of numbers
  -- in xs and ys is a lower bound of n (if _≤_ is interpreted as an
  -- ordering relation).

  Below : (Nat → Nat → Set) → (Nat → Nat → Nat) → S → S → Nat → Set a
  Below _≤_ _∙_ xs ys n =
    ∃₂ λ l m → ((l ∙ m) ≤ n) × l ∈ xs × m ∈ ys

  -- In _∙_ xs ys n means that some combination of numbers in xs and
  -- ys is a lower bound of n, and some combination of numbers in xs
  -- and ys is an upper bound of n.

  In : (Nat → Nat → Nat) → S → S → Nat → Set a
  In _∙_ xs ys n =
    Below N._≤_ _∙_ xs ys n × Below (flip N._≤_) _∙_ xs ys n

  ----------------------------------------------------------------------
  -- Some lemmas

  open Tools.Algebra S

  -- The following lemmas are proved under the assumption that Ext is
  -- inhabited.

  module _ (ext : Ext) where

    --------------------------------------------------------------------
    -- Lemmas related to _∪_

    -- The union operator forms a semilattice.

    ∪-semilattice : IsMeetSemilattice _∪_
    ∪-semilattice = record
      { isBand = record
        { isSemigroup = record
          { isMagma = record
            { isEquivalence = PE.isEquivalence
            ; ∙-cong        = cong₂ _∪_
            }
          ; assoc = ∪-assoc
          }
        ; idem = ∪-idem
        }
      ; comm = ∪-comm
      }
      where
      ∪-assoc : Associative _∪_
      ∪-assoc xs ys zs = ≡⇔ ext .proj₂ λ n →
        n ∈ (xs ∪ ys) ∪ zs                                            ⇔⟨ ∈∪⇔ ⟩
        Closure (λ n → n ∈ xs ∪ ys ⊎ n ∈ zs) n                        ⇔⟨ (Closure-cong-⇔ λ _ → ∈∪⇔ ⊎-cong-⇔ id⇔) ⟩
        Closure (λ n → Closure (λ n → n ∈ xs ⊎ n ∈ ys) n ⊎ n ∈ zs) n  ⇔⟨ Closure-⊎ˡ ⟩
        Closure (λ n → (n ∈ xs ⊎ n ∈ ys) ⊎ n ∈ zs) n                  ⇔⟨ (Closure-cong-⇔ λ _ → ⊎-assoc-⇔) ⟩
        Closure (λ n → n ∈ xs ⊎ (n ∈ ys ⊎ n ∈ zs)) n                  ⇔˘⟨ Closure-⊎ʳ ⟩
        Closure (λ n → n ∈ xs ⊎ Closure (λ n → n ∈ ys ⊎ n ∈ zs) n) n  ⇔˘⟨ (Closure-cong-⇔ λ _ → id⇔ ⊎-cong-⇔ ∈∪⇔) ⟩
        Closure (λ n → n ∈ xs ⊎ n ∈ ys ∪ zs) n                        ⇔˘⟨ ∈∪⇔ ⟩
        n ∈ xs ∪ (ys ∪ zs)                                            □⇔

      ∪-idem : Idempotent _∪_
      ∪-idem xs = ≡⇔ ext .proj₂ λ n →
        n ∈ xs ∪ xs                        ⇔⟨ ∈∪⇔ ⟩
        Closure (λ n → n ∈ xs ⊎ n ∈ xs) n  ⇔⟨ (Closure-cong-⇔ λ _ → ⊎-idem-⇔) ⟩
        Closure (_∈ xs) n                  ⇔⟨ Closure⇔ ⟩
        n ∈ xs                             □⇔

      ∪-comm : Commutative _∪_
      ∪-comm xs ys = ≡⇔ ext .proj₂ λ n →
        n ∈ xs ∪ ys                        ⇔⟨ ∈∪⇔ ⟩
        Closure (λ n → n ∈ xs ⊎ n ∈ ys) n  ⇔⟨ (Closure-cong-⇔ λ _ → ⊎-comm-⇔) ⟩
        Closure (λ n → n ∈ ys ⊎ n ∈ xs) n  ⇔˘⟨ ∈∪⇔ ⟩
        n ∈ ys ∪ xs                        □⇔

    open IsMeetSemilattice ∪-semilattice
      using () renaming (comm to ∪-comm)

    -- Union is positive.

    ∪-positive : xs ∪ ys ≡ 𝟘 → xs ≡ 𝟘 × ys ≡ 𝟘
    ∪-positive eq =
      ∪-positiveˡ eq , ∪-positiveˡ (trans (∪-comm _ _) eq)
      where
      ∪-positiveˡ : xs ∪ ys ≡ 𝟘 → xs ≡ 𝟘
      ∪-positiveˡ {xs = xs} {ys = ys} =
        xs ∪ ys ≡ 𝟘                      →⟨ proj₂ ∘→ ≡[]→ ⟩
        (∀ n → n ∈ xs ∪ ys → n ≡ 0)      →⟨ (_∘→ ∈∪⇔ .proj₂ ∘→ included ∘→ inj₁) ∘→_ ⟩
        (∀ n → n ∈ xs → n ≡ 0)           →⟨ (λ hyp → subst (_∈ _) (uncurry hyp non-empty) (non-empty .proj₂) , hyp) ⟩
        0 ∈ xs × (∀ n → n ∈ xs → n ≡ 0)  ⇔˘⟨ ≡[]⇔ ext ⟩→
        xs ≡ 𝟘                           □

    --------------------------------------------------------------------
    -- Lemmas for an arbitrary binary operator that satisfies a
    -- certain property

    module Operator
      {_∙_ : Nat → Nat → Nat}
      {ε : Nat}
      (∙-ε-commutative-monoid :
         Tools.Algebra.IsCommutativeMonoid Nat _∙_ ε)
      (∙-monotone : _∙_ Preserves₂ N._≤_ ⟶ N._≤_ ⟶ N._≤_)
      (_⊙_ : S → S → S)
      (∈⊙⇔ :
         ∀ {n xs ys} →
         n ∈ (xs ⊙ ys) ⇔
         Closure (λ n → ∃₂ λ l m → (l ∙ m) ≡ n × l ∈ xs × m ∈ ys) n)
      where

      private
        module M =
          Tools.Algebra.IsCommutativeMonoid Nat ∙-ε-commutative-monoid

      -- One can express membership in xs ⊙ ys using In.

      ∈⇔In : n ∈ (xs ⊙ ys) ⇔ In _∙_ xs ys n
      ∈⇔In {n = n} {xs = xs} {ys = ys} =
        n ∈ (xs ⊙ ys)                                               ⇔⟨ ∈⊙⇔ ⟩
        Closure (λ n → ∃₂ λ l m → (l ∙ m) ≡ n × l ∈ xs × m ∈ ys) n  ⇔⟨ (λ ( l , m , l≤n , n≤m
                                                                          , (l₁ , m₁ , l₁+m₁≡l , l₁∈xs , m₁∈ys)
                                                                          , (l₂ , m₂ , l₂+m₂≡m , l₂∈xs , m₂∈ys)
                                                                          ) →
                                                                            (l₁ , m₁ , subst (N._≤ _) (sym l₁+m₁≡l) l≤n , l₁∈xs , m₁∈ys)
                                                                          , (l₂ , m₂ , subst (_ N.≤_) (sym l₂+m₂≡m) n≤m , l₂∈xs , m₂∈ys))
                                                                     , (λ ( (l₁ , m₁ , l₁+m₁≤n , l₁∈xs , m₁∈ys)
                                                                          , (l₂ , m₂ , n≤l₂+m₂ , l₂∈xs , m₂∈ys)
                                                                          ) →
                                                                            (l₁ ∙ m₁) , (l₂ ∙ m₂) , l₁+m₁≤n , n≤l₂+m₂
                                                                          , (l₁ , m₁ , refl , l₁∈xs , m₁∈ys)
                                                                          , (l₂ , m₂ , refl , l₂∈xs , m₂∈ys))
                                                                     ⟩
        In _∙_ xs ys n                                              □⇔

      -- The binary operator _⊙_ and [ ε ] form a commutative monoid.

      commutative-monoid : IsCommutativeMonoid _⊙_ [ ε ]
      commutative-monoid = record
        { isMonoid = record
          { isSemigroup = record
            { isMagma = record
              { isEquivalence = PE.isEquivalence
              ; ∙-cong        = cong₂ _⊙_
              }
            ; assoc = assoc
            }
          ; identity = identity
          }
        ; comm = comm
        }
        where
        open N.≤-Reasoning

        assoc : Associative _⊙_
        assoc xs ys zs = ≡⇔ ext .proj₂ λ n →
          n ∈ (xs ⊙ ys) ⊙ zs                                       ⇔⟨ ∈⇔In ⟩

          (∃₂ λ l m → (l ∙ m) N.≤ n × l ∈ xs ⊙ ys × m ∈ zs) ×
          (∃₂ λ l m → n N.≤ (l ∙ m) × l ∈ xs ⊙ ys × m ∈ zs)        ⇔⟨ (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → ∈⇔In ×-cong-⇔ id⇔)
                                                                        ×-cong-⇔
                                                                      (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → ∈⇔In ×-cong-⇔ id⇔) ⟩
          (∃₂ λ l m →
           (l ∙ m) N.≤ n ×
           ((∃₂ λ l′ m′ → (l′ ∙ m′) N.≤ l × l′ ∈ xs × m′ ∈ ys) ×
            (∃₂ λ l′ m′ → l N.≤ (l′ ∙ m′) × l′ ∈ xs × m′ ∈ ys)) ×
           m ∈ zs) ×
          (∃₂ λ l m →
           n N.≤ (l ∙ m) ×
           ((∃₂ λ l′ m′ → (l′ ∙ m′) N.≤ l × l′ ∈ xs × m′ ∈ ys) ×
            (∃₂ λ l′ m′ → l N.≤ (l′ ∙ m′) × l′ ∈ xs × m′ ∈ ys)) ×
           m ∈ zs)                                                 ⇔⟨ ( (λ ( l₁ , m₁ , l₁m₁≤n
                                                                           , ( (l₂ , m₂ , l₂m₂≤l₁ , l₂∈xs , m₂∈ys)
                                                                             , _
                                                                             )
                                                                           , m₁∈zs
                                                                           ) →
                                                                             l₂
                                                                           , (m₂ ∙ m₁)
                                                                           , (begin
                                                                                (l₂ ∙ (m₂ ∙ m₁))  ≡˘⟨ M.assoc _ _ _ ⟩
                                                                                ((l₂ ∙ m₂) ∙ m₁)  ≤⟨ ∙-monotone l₂m₂≤l₁ N.≤-refl ⟩
                                                                                (l₁ ∙ m₁)         ≤⟨ l₁m₁≤n ⟩
                                                                                n                 ∎)
                                                                           , l₂∈xs
                                                                           , ( (m₂ , m₁ , N.≤-refl , m₂∈ys , m₁∈zs)
                                                                             , (m₂ , m₁ , N.≤-refl , m₂∈ys , m₁∈zs)
                                                                             ))
                                                                      , (λ ( l₁ , m₁ , l₁m₁≤n , l₁∈xs
                                                                           , ( (l₂ , m₂ , l₂m₂≤m₁ , l₂∈ys , m₂∈zs)
                                                                             , _
                                                                             )
                                                                           ) →
                                                                             (l₁ ∙ l₂)
                                                                           , m₂
                                                                           , (begin
                                                                                ((l₁ ∙ l₂) ∙ m₂)  ≡⟨ M.assoc _ _ _ ⟩
                                                                                (l₁ ∙ (l₂ ∙ m₂))  ≤⟨ ∙-monotone N.≤-refl l₂m₂≤m₁ ⟩
                                                                                (l₁ ∙ m₁)         ≤⟨ l₁m₁≤n ⟩
                                                                                n                 ∎)
                                                                           , ( (l₁ , l₂ , N.≤-refl , l₁∈xs , l₂∈ys)
                                                                             , (l₁ , l₂ , N.≤-refl , l₁∈xs , l₂∈ys)
                                                                             )
                                                                           , m₂∈zs)
                                                                      )
                                                                        ×-cong-⇔
                                                                      ( (λ ( l₄ , m₄ , n≤l₄m₄
                                                                           , ( _
                                                                             , (l₆ , m₆ , l₄≤l₆m₆ , l₆∈xs , m₆∈ys)
                                                                             )
                                                                           , m₄∈zs
                                                                           ) →
                                                                             l₆
                                                                           , (m₆ ∙ m₄)
                                                                           , (begin
                                                                                n                 ≤⟨ n≤l₄m₄ ⟩
                                                                                (l₄ ∙ m₄)         ≤⟨ ∙-monotone l₄≤l₆m₆ N.≤-refl ⟩
                                                                                ((l₆ ∙ m₆) ∙ m₄)  ≡⟨ M.assoc _ _ _ ⟩
                                                                                (l₆ ∙ (m₆ ∙ m₄))  ∎)
                                                                           , l₆∈xs
                                                                           , ( (m₆ , m₄ , N.≤-refl , m₆∈ys , m₄∈zs)
                                                                             , (m₆ , m₄ , N.≤-refl , m₆∈ys , m₄∈zs)
                                                                             ))
                                                                      , (λ ( l₄ , m₄ , n≤l₄m₄ , l₄∈xs
                                                                           , ( _
                                                                             , (l₆ , m₆ , m₄≤l₆m₆ , l₆∈ys , m₆∈zs)
                                                                             )
                                                                           ) →
                                                                             (l₄ ∙ l₆)
                                                                           , m₆
                                                                           , (begin
                                                                                n                 ≤⟨ n≤l₄m₄ ⟩
                                                                                (l₄ ∙ m₄)         ≤⟨ ∙-monotone N.≤-refl m₄≤l₆m₆ ⟩
                                                                                (l₄ ∙ (l₆ ∙ m₆))  ≡˘⟨ M.assoc _ _ _ ⟩
                                                                                ((l₄ ∙ l₆) ∙ m₆)  ∎)
                                                                           , ( (l₄ , l₆ , N.≤-refl , l₄∈xs , l₆∈ys)
                                                                             , (l₄ , l₆ , N.≤-refl , l₄∈xs , l₆∈ys)
                                                                             )
                                                                           , m₆∈zs)
                                                                      )
                                                                    ⟩
          (∃₂ λ l m →
           (l ∙ m) N.≤ n ×
           l ∈ xs ×
           (∃₂ λ l′ m′ → (l′ ∙ m′) N.≤ m × l′ ∈ ys × m′ ∈ zs) ×
           (∃₂ λ l′ m′ → m N.≤ (l′ ∙ m′) × l′ ∈ ys × m′ ∈ zs)) ×
          (∃₂ λ l m →
           n N.≤ (l ∙ m) ×
           l ∈ xs ×
           (∃₂ λ l′ m′ → (l′ ∙ m′) N.≤ m × l′ ∈ ys × m′ ∈ zs) ×
           (∃₂ λ l′ m′ → m N.≤ (l′ ∙ m′) × l′ ∈ ys × m′ ∈ zs))     ⇔˘⟨ (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → ∈⇔In)
                                                                         ×-cong-⇔
                                                                       (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → ∈⇔In) ⟩
          (∃₂ λ l m → (l ∙ m) N.≤ n × l ∈ xs × m ∈ ys ⊙ zs) ×
          (∃₂ λ l m → n N.≤ (l ∙ m) × l ∈ xs × m ∈ ys ⊙ zs)        ⇔˘⟨ ∈⇔In ⟩

          n ∈ xs ⊙ (ys ⊙ zs)                                       □⇔

        comm : Commutative _⊙_
        comm xs ys = ≡⇔ ext .proj₂ λ n →
          n ∈ xs ⊙ ys                                     ⇔⟨ ∈⇔In ⟩

          (∃₂ λ l m → (l ∙ m) N.≤ n × l ∈ xs × m ∈ ys) ×
          (∃₂ λ l m → n N.≤ (l ∙ m) × l ∈ xs × m ∈ ys)    ⇔⟨ (λ ( (l₁ , m₁ , l₁m₁≤n , l₁∈xs , m₁∈ys)
                                                                , (l₂ , m₂ , n≤l₂m₂ , l₂∈xs , m₂∈ys)
                                                                ) →
                                                                  (m₁ , l₁ , subst (N._≤ n) (M.comm _ _) l₁m₁≤n , m₁∈ys , l₁∈xs)
                                                                , (m₂ , l₂ , subst (n N.≤_) (M.comm _ _) n≤l₂m₂ , m₂∈ys , l₂∈xs))
                                                           , (λ ( (l₁ , m₁ , l₁m₁≤n , l₁∈ys , m₁∈xs)
                                                                , (l₂ , m₂ , n≤l₂m₂ , l₂∈ys , m₂∈xs)
                                                                ) →
                                                                  (m₁ , l₁ , subst (N._≤ n) (M.comm _ _) l₁m₁≤n , m₁∈xs , l₁∈ys)
                                                                , (m₂ , l₂ , subst (n N.≤_) (M.comm _ _) n≤l₂m₂ , m₂∈xs , l₂∈ys))
                                                           ⟩
          (∃₂ λ l m → (l ∙ m) N.≤ n × l ∈ ys × m ∈ xs) ×
          (∃₂ λ l m → n N.≤ (l ∙ m) × l ∈ ys × m ∈ xs)    ⇔˘⟨ ∈⇔In ⟩

          n ∈ ys ⊙ xs                                     □⇔

        identityˡ : LeftIdentity [ ε ] _⊙_
        identityˡ xs = ≡⇔ ext .proj₂ λ n →
          n ∈ [ ε ] ⊙ xs                                     ⇔⟨ ∈⇔In ⟩

          (∃₂ λ l m → (l ∙ m) N.≤ n × l ∈ [ ε ] × m ∈ xs) ×
          (∃₂ λ l m → n N.≤ (l ∙ m) × l ∈ [ ε ] × m ∈ xs)    ⇔⟨ (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → ∈[]⇔ ×-cong-⇔ id⇔)
                                                                  ×-cong-⇔
                                                                (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → ∈[]⇔ ×-cong-⇔ id⇔) ⟩
          (∃₂ λ l m → (l ∙ m) N.≤ n × l ≡ ε × m ∈ xs) ×
          (∃₂ λ l m → n N.≤ (l ∙ m) × l ≡ ε × m ∈ xs)        ⇔⟨ (λ { ( (.ε , m₁ , εm₁≤n , refl , m₁∈xs)
                                                                     , (.ε , m₂ , n≤εm₂ , refl , m₂∈xs)
                                                                     ) →
                                                                     interval
                                                                       ( _ , _
                                                                       , subst (N._≤ _) (M.identityˡ _) εm₁≤n
                                                                       , subst (_ N.≤_) (M.identityˡ _) n≤εm₂
                                                                       , m₁∈xs , m₂∈xs
                                                                       ) })
                                                              , (λ n∈xs →
                                                                     (ε , n , N.≤-reflexive      (M.identityˡ _)  , refl , n∈xs)
                                                                   , (ε , n , N.≤-reflexive (sym (M.identityˡ _)) , refl , n∈xs))
                                                              ⟩

          n ∈ xs                                             □⇔

        identity : Identity [ ε ] _⊙_
        identity = identityˡ , comm∧idˡ⇒idʳ comm identityˡ

      -- The binary operator _⊙_ distributes over union.

      distrib-∪ : _⊙_ DistributesOver _∪_
      distrib-∪ =
          distribˡ-∪
        , comm∧distrˡ⇒distrʳ
            (IsCommutativeMonoid.comm commutative-monoid)
            distribˡ-∪
        where
        distribˡ-∪ : _⊙_ DistributesOverˡ _∪_
        distribˡ-∪ xs ys zs = ≡⇔ ext .proj₂ λ n →
          n ∈ (xs ⊙ (ys ∪ zs))                                         ⇔⟨ ∈⇔In ⟩

          (∃₂ λ l m → (l ∙ m) N.≤ n × l ∈ xs × m ∈ ys ∪ zs) ×
          (∃₂ λ l m → n N.≤ (l ∙ m) × l ∈ xs × m ∈ ys ∪ zs)            ⇔⟨ (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ →
                                                                           ∈∪⇔)
                                                                            ×-cong-⇔
                                                                          (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ →
                                                                           ∈∪⇔) ⟩
          (∃₂ λ l m → (l ∙ m) N.≤ n × l ∈ xs ×
           Closure (λ m → m ∈ ys ⊎ m ∈ zs) m) ×
          (∃₂ λ l m → n N.≤ (l ∙ m) × l ∈ xs ×
           Closure (λ m → m ∈ ys ⊎ m ∈ zs) m)                          ⇔⟨ (λ ( ( l₁ , m₁ , l₁m₁≤n , l₁∈xs
                                                                               , l₂ , _ , l₂≤m₁ , _ , p₁ , _
                                                                               )
                                                                             , ( l₃ , m₃ , n≤l₃m₃ , l₃∈xs
                                                                               , _ , m₄ , _ , m₃≤m₄ , _ , p₄
                                                                               )
                                                                             ) →
                                                                               (l₁ ∙ l₂) , (l₃ ∙ m₄)
                                                                             , (begin
                                                                                  (l₁ ∙ l₂)  ≤⟨ ∙-monotone N.≤-refl l₂≤m₁ ⟩
                                                                                  (l₁ ∙ m₁)  ≤⟨ l₁m₁≤n ⟩
                                                                                  n          ∎)
                                                                             , (begin
                                                                                  n          ≤⟨ n≤l₃m₃ ⟩
                                                                                  (l₃ ∙ m₃)  ≤⟨ ∙-monotone N.≤-refl m₃≤m₄ ⟩
                                                                                  (l₃ ∙ m₄)  ∎)
                                                                             , (case p₁ of λ where
                                                                                  (inj₁ l₂∈ys) →
                                                                                    inj₁ (l₁ , l₂ , refl , l₁∈xs , l₂∈ys)
                                                                                  (inj₂ l₂∈zs) →
                                                                                    inj₂ (l₁ , l₂ , refl , l₁∈xs , l₂∈zs))
                                                                             , (case p₄ of λ where
                                                                                  (inj₁ m₄∈ys) →
                                                                                    inj₁ (l₃ , m₄ , refl , l₃∈xs , m₄∈ys)
                                                                                  (inj₂ m₄∈zs) →
                                                                                    inj₂ (l₃ , m₄ , refl , l₃∈xs , m₄∈zs)))
                                                                        , (λ where
                                                                              (.(l₁ ∙ m₁) , .(l₂ ∙ m₂) , l₁m₁≤n , n≤l₂m₂ ,
                                                                               inj₁ (l₁ , m₁ , refl , l₁∈xs , m₁∈ys) ,
                                                                               inj₁ (l₂ , m₂ , refl , l₂∈xs , m₂∈ys)) →
                                                                                  (l₁ , m₁ , l₁m₁≤n , l₁∈xs , included (inj₁ m₁∈ys))
                                                                                , (l₂ , m₂ , n≤l₂m₂ , l₂∈xs , included (inj₁ m₂∈ys))
                                                                              (.(l₁ ∙ m₁) , .(l₂ ∙ m₂) , l₁m₁≤n , n≤l₂m₂ ,
                                                                               inj₁ (l₁ , m₁ , refl , l₁∈xs , m₁∈ys) ,
                                                                               inj₂ (l₂ , m₂ , refl , l₂∈xs , m₂∈zs)) →
                                                                                  (l₁ , m₁ , l₁m₁≤n , l₁∈xs , included (inj₁ m₁∈ys))
                                                                                , (l₂ , m₂ , n≤l₂m₂ , l₂∈xs , included (inj₂ m₂∈zs))
                                                                              (.(l₁ ∙ m₁) , .(l₂ ∙ m₂) , l₁m₁≤n , n≤l₂m₂ ,
                                                                               inj₂ (l₁ , m₁ , refl , l₁∈xs , m₁∈zs) ,
                                                                               inj₁ (l₂ , m₂ , refl , l₂∈xs , m₂∈ys)) →
                                                                                  (l₁ , m₁ , l₁m₁≤n , l₁∈xs , included (inj₂ m₁∈zs))
                                                                                , (l₂ , m₂ , n≤l₂m₂ , l₂∈xs , included (inj₁ m₂∈ys))
                                                                              (.(l₁ ∙ m₁) , .(l₂ ∙ m₂) , l₁m₁≤n , n≤l₂m₂ ,
                                                                               inj₂ (l₁ , m₁ , refl , l₁∈xs , m₁∈zs) ,
                                                                               inj₂ (l₂ , m₂ , refl , l₂∈xs , m₂∈zs)) →
                                                                                  (l₁ , m₁ , l₁m₁≤n , l₁∈xs , included (inj₂ m₁∈zs))
                                                                                , (l₂ , m₂ , n≤l₂m₂ , l₂∈xs , included (inj₂ m₂∈zs)))
                                                                        ⟩
          Closure
            (λ n →
               (∃₂ λ l m → (l ∙ m) ≡ n × l ∈ xs × m ∈ ys) ⊎
               (∃₂ λ l m → (l ∙ m) ≡ n × l ∈ xs × m ∈ zs))
            n                                                          ⇔˘⟨ Closure-⊎ ⟩

          Closure
            (λ n →
               Closure
                 (λ n → ∃₂ λ l m → (l ∙ m) ≡ n × l ∈ xs × m ∈ ys) n ⊎
               Closure
                 (λ n → ∃₂ λ l m → (l ∙ m) ≡ n × l ∈ xs × m ∈ zs) n)
            n                                                          ⇔˘⟨ (Closure-cong-⇔ λ _ → ∈⊙⇔ ⊎-cong-⇔ ∈⊙⇔) ⟩

          Closure (λ n → n ∈ (xs ⊙ ys) ⊎ n ∈ (xs ⊙ zs)) n              ⇔˘⟨ ∈∪⇔ ⟩

          n ∈ (xs ⊙ ys) ∪ (xs ⊙ zs)                                    □⇔
          where
          open N.≤-Reasoning

    --------------------------------------------------------------------
    -- Lemmas related to _+_

    private
      module Addition =
        Operator N.+-0-isCommutativeMonoid N.+-mono-≤ _+_ ∈+⇔

    -- One can express membership in xs + ys using In.

    ∈+⇔′ : n ∈ xs + ys ⇔ In N._+_ xs ys n
    ∈+⇔′ = Addition.∈⇔In

    -- Addition and 𝟘 form a commutative monoid.

    +-𝟘-commutative-monoid : IsCommutativeMonoid _+_ 𝟘
    +-𝟘-commutative-monoid = Addition.commutative-monoid

    open IsCommutativeMonoid +-𝟘-commutative-monoid
      using () renaming (comm to +-comm)

    -- Addition distributes over union.

    +-distrib-∪ : _+_ DistributesOver _∪_
    +-distrib-∪ = Addition.distrib-∪

    -- Addition is positive.

    +-positive : xs + ys ≡ 𝟘 → xs ≡ 𝟘 × ys ≡ 𝟘
    +-positive eq =
      +-positiveˡ eq , +-positiveˡ (trans (+-comm _ _) eq)
      where
      lemma : ∀ xs ys → 0 ∈ xs + ys → 0 ∈ xs × 0 ∈ ys
      lemma xs ys =
        0 ∈ xs + ys                                     ⇔⟨ ∈+⇔′ ⟩→

        (∃₂ λ l m → l N.+ m N.≤ 0 × l ∈ xs × m ∈ ys) ×
        (∃₂ λ l m → 0 N.≤ l N.+ m × l ∈ xs × m ∈ ys)    →⟨ (λ { ((0      , .0 , N.z≤n , hyp) , _) → hyp
                                                              ; ((N.1+ _ , _  , ()    , _)   , _)
                                                              }) ⟩
        0 ∈ xs × 0 ∈ ys                                 □

      +-positiveˡ : xs + ys ≡ 𝟘 → xs ≡ 𝟘
      +-positiveˡ {xs = xs} {ys = ys} =
        xs + ys ≡ 𝟘                                      →⟨ ≡[]→ ⟩

        0 ∈ xs + ys × (∀ n → n ∈ xs + ys → n ≡ 0)        →⟨ Σ.map (lemma _ _) idᶠ ⟩

        (0 ∈ xs × 0 ∈ ys) × (∀ n → n ∈ xs + ys → n ≡ 0)  →⟨ (λ ((0∈xs , 0∈ys) , hyp) →
                                                                 0∈xs
                                                               , (λ n →
          n ∈ xs                                                    →⟨ (λ n∈xs → ∈+⇔′ .proj₂
                                                                          ( (n , 0 , N.≤-reflexive      (N.+-identityʳ _)  , n∈xs , 0∈ys)
                                                                          , (n , 0 , N.≤-reflexive (sym (N.+-identityʳ _)) , n∈xs , 0∈ys)
                                                                          )) ⟩
          n ∈ xs + ys                                               →⟨ hyp _ ⟩
          n ≡ 0                                                     □)) ⟩

        0 ∈ xs × (∀ n → n ∈ xs → n ≡ 0)                  ⇔˘⟨ ≡[]⇔ ext ⟩→

        xs ≡ 𝟘                                           □

    --------------------------------------------------------------------
    -- Lemmas related to _·_

    private
      module Multiplication =
        Operator N.*-1-isCommutativeMonoid N.*-mono-≤ _·_ ∈·⇔

    -- One can express membership in xs · ys using In.

    ∈·⇔′ : n ∈ xs · ys ⇔ In N._*_ xs ys n
    ∈·⇔′ = Multiplication.∈⇔In

    -- Multiplication and 𝟙 form a commutative monoid.

    ·-𝟙-commutative-monoid : IsCommutativeMonoid _·_ 𝟙
    ·-𝟙-commutative-monoid = Multiplication.commutative-monoid

    open IsCommutativeMonoid ·-𝟙-commutative-monoid
      using () renaming (comm to ·-comm)

    -- Multiplication distributes over union.

    ·-distrib-∪ : _·_ DistributesOver _∪_
    ·-distrib-∪ = Multiplication.distrib-∪

    -- 𝟘 is a zero for multiplication.

    ·-zero : Zero 𝟘 _·_
    ·-zero = ·-zeroˡ , comm∧zeˡ⇒zeʳ ·-comm ·-zeroˡ
      where
      ·-zeroˡ : LeftZero 𝟘 _·_
      ·-zeroˡ xs = ≡⇔ ext .proj₂ λ n →
        n ∈ 𝟘 · xs                                                 ⇔⟨ ∈·⇔ ⟩
        Closure (λ n → ∃₂ λ l m → l N.* m ≡ n × l ∈ 𝟘 × m ∈ xs) n  ⇔⟨ (Closure-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ →
                                                                       ∈[]⇔ ×-cong-⇔ id⇔) ⟩
        Closure (λ n → ∃₂ λ l m → l N.* m ≡ n × l ≡ 0 × m ∈ xs) n  ⇔⟨ (Closure-cong-⇔ λ _ →
                                                                         (λ { (.0 , m , refl , refl , m∈xs) → m , refl , m∈xs })
                                                                       , (λ { (m , refl , m∈xs) → 0 , m , refl , refl , m∈xs })) ⟩
        Closure (λ n → ∃ λ m → n ≡ 0 × m ∈ xs) n                   ⇔⟨ Closure-at-most-one
                                                                        (λ { (_ , refl , _) (_ , refl , _) → refl }) ⟩
        (∃ λ m → n ≡ 0 × m ∈ xs)                                   ⇔⟨ (λ { (_ , n≡0 , _) → n≡0 })
                                                                    , (λ { n≡0 → _ , n≡0 , non-empty .proj₂ })
                                                                    ⟩
        n ≡ 0                                                      ⇔˘⟨ ∈[]⇔ ⟩
        n ∈ 𝟘                                                      □⇔

    -- The zero-product property holds.

    zero-product : xs · ys ≡ 𝟘 → xs ≡ 𝟘 ⊎ ys ≡ 𝟘
    zero-product {xs = xs} {ys = ys} =
      lemma (is-𝟘? xs) (is-𝟘? ys)
      where
      lemma :
        (Ext → xs ≡ 𝟘) ⊎ xs ≢ 𝟘 →
        (Ext → ys ≡ 𝟘) ⊎ ys ≢ 𝟘 →
        xs · ys ≡ 𝟘 → xs ≡ 𝟘 ⊎ ys ≡ 𝟘
      lemma (inj₁ xs≡𝟘) _           = λ _ → inj₁ (xs≡𝟘 ext)
      lemma _           (inj₁ ys≡𝟘) = λ _ → inj₂ (ys≡𝟘 ext)
      lemma (inj₂ xs≢𝟘) (inj₂ ys≢𝟘) =
        xs · ys ≡ 𝟘                                                    →⟨ ≡[]→ ⟩

        0 ∈ xs · ys × (∀ n → n ∈ xs · ys → n ≡ 0)                      →⟨ proj₂ ⟩

        (∀ n → n ∈ xs · ys → n ≡ 0)                                    ⇔⟨ (Π-cong-⇔ λ _ → ∈·⇔ →-cong-⇔ id⇔) ⟩→

        (∀ n →
         Closure
           (λ n → ∃₂ λ m₁ m₂ → m₁ N.* m₂ ≡ n × m₁ ∈ xs × m₂ ∈ ys) n →
         n ≡ 0)                                                        →⟨ (_∘→ included) ∘→_ ⟩

        (∀ n → (∃₂ λ m₁ m₂ → m₁ N.* m₂ ≡ n × m₁ ∈ xs × m₂ ∈ ys) →
         n ≡ 0)                                                        →⟨ multiplication-lemma
                                                                            (xs≢𝟘 ∘→ ≡[]⇔ ext .proj₂)
                                                                            (ys≢𝟘 ∘→ ≡[]⇔ ext .proj₂) ⟩

        ⊥                                                              →⟨ ⊥-elim ⟩

        xs ≡ 𝟘 ⊎ ys ≡ 𝟘                                                □

    --------------------------------------------------------------------
    -- Another distributivity law

    -- Multiplication distributes over addition.

    ·-distrib-+ : _·_ DistributesOver _+_
    ·-distrib-+ = ·-distribˡ-+ , comm∧distrˡ⇒distrʳ ·-comm ·-distribˡ-+
      where
      ·-distribˡ-+ : _·_ DistributesOverˡ _+_
      ·-distribˡ-+ xs ys zs = ≡⇔ ext .proj₂ λ n →
        n ∈ xs · (ys + zs)                                        ⇔⟨ ∈·⇔′ ⟩

        (∃₂ λ l m → l N.* m N.≤ n × l ∈ xs × m ∈ ys + zs) ×
        (∃₂ λ l m → n N.≤ l N.* m × l ∈ xs × m ∈ ys + zs)         ⇔⟨ (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ →
                                                                      ∈+⇔′)
                                                                       ×-cong-⇔
                                                                     (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ →
                                                                      ∈+⇔′) ⟩
        (∃₂ λ l m → l N.* m N.≤ n × l ∈ xs ×
         (∃₂ λ l′ m′ → l′ N.+ m′ N.≤ m × l′ ∈ ys × m′ ∈ zs) ×
         (∃₂ λ l′ m′ → m N.≤ l′ N.+ m′ × l′ ∈ ys × m′ ∈ zs)) ×
        (∃₂ λ l m → n N.≤ l N.* m × l ∈ xs ×
         (∃₂ λ l′ m′ → l′ N.+ m′ N.≤ m × l′ ∈ ys × m′ ∈ zs) ×
         (∃₂ λ l′ m′ → m N.≤ l′ N.+ m′ × l′ ∈ ys × m′ ∈ zs))      ⇔⟨ lemma₁ n ×-cong-⇔ lemma₂ n ⟩

        (∃₂ λ l m → l N.+ m N.≤ n ×
         ((∃₂ λ l′ m′ → l′ N.* m′ N.≤ l × l′ ∈ xs × m′ ∈ ys) ×
          (∃₂ λ l′ m′ → l N.≤ l′ N.* m′ × l′ ∈ xs × m′ ∈ ys)) ×
         ((∃₂ λ l′ m′ → l′ N.* m′ N.≤ m × l′ ∈ xs × m′ ∈ zs) ×
          (∃₂ λ l′ m′ → m N.≤ l′ N.* m′ × l′ ∈ xs × m′ ∈ zs))) ×
        (∃₂ λ l m → n N.≤ l N.+ m ×
         ((∃₂ λ l′ m′ → l′ N.* m′ N.≤ l × l′ ∈ xs × m′ ∈ ys) ×
          (∃₂ λ l′ m′ → l N.≤ l′ N.* m′ × l′ ∈ xs × m′ ∈ ys)) ×
         ((∃₂ λ l′ m′ → l′ N.* m′ N.≤ m × l′ ∈ xs × m′ ∈ zs) ×
          (∃₂ λ l′ m′ → m N.≤ l′ N.* m′ × l′ ∈ xs × m′ ∈ zs)))    ⇔˘⟨ (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ →
                                                                       ∈·⇔′ ×-cong-⇔ ∈·⇔′)
                                                                        ×-cong-⇔
                                                                      (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ →
                                                                       ∈·⇔′ ×-cong-⇔ ∈·⇔′) ⟩
        (∃₂ λ l m → l N.+ m N.≤ n × l ∈ xs · ys × m ∈ xs · zs) ×
        (∃₂ λ l m → n N.≤ l N.+ m × l ∈ xs · ys × m ∈ xs · zs)    ⇔˘⟨ ∈+⇔′ ⟩

        n ∈ xs · ys + xs · zs                                     □⇔
        where
        open N.≤-Reasoning

        lemma₁ = λ n →
            (λ ( l₁ , m₁ , l₁m₁≤n , l₁∈xs
               , (l₂ , m₂ , l₂+m₂≤m₁ , l₂∈ys , m₂∈zs)
               , _
               ) →
                 l₁ N.* l₂ , l₁ N.* m₂
               , (begin
                    l₁ N.* l₂ N.+ l₁ N.* m₂  ≡˘⟨ N.*-distribˡ-+ l₁ _ _ ⟩
                    l₁ N.* (l₂ N.+ m₂)       ≤⟨ N.*-mono-≤ (N.≤-refl {x = l₁}) l₂+m₂≤m₁ ⟩
                    l₁ N.* m₁                ≤⟨ l₁m₁≤n ⟩
                    n                        ∎)
               , ( (l₁ , l₂ , N.≤-refl , l₁∈xs , l₂∈ys)
                 , (l₁ , l₂ , N.≤-refl , l₁∈xs , l₂∈ys)
                 )
               , ( (l₁ , m₂ , N.≤-refl , l₁∈xs , m₂∈zs)
                 , (l₁ , m₂ , N.≤-refl , l₁∈xs , m₂∈zs)
                 ))
          , (λ ( l₁ , m₁ , l₁+m₁≤n
               , ( (l₂ , m₂ , l₂m₂≤l₁ , l₂∈xs , m₂∈ys)
                 , _
                 )
               , ( (l₃ , m₃ , l₃m₃≤m₁ , l₃∈xs , m₃∈zs)
                 , _
                 )
               ) →
               case N.≤-total l₂ l₃ of λ where
                 (inj₁ l₂≤l₃) →
                     l₂ , m₂ N.+ m₃
                   , (begin
                        l₂ N.* (m₂ N.+ m₃)       ≡⟨ N.*-distribˡ-+ l₂ _ _ ⟩
                        l₂ N.* m₂ N.+ l₂ N.* m₃  ≤⟨ N.+-mono-≤ N.≤-refl (N.*-mono-≤ l₂≤l₃ N.≤-refl) ⟩
                        l₂ N.* m₂ N.+ l₃ N.* m₃  ≤⟨ N.+-mono-≤ l₂m₂≤l₁ l₃m₃≤m₁ ⟩
                        l₁ N.+ m₁                ≤⟨ l₁+m₁≤n ⟩
                        n                        ∎)
                   , l₂∈xs
                   , (m₂ , m₃ , N.≤-refl , m₂∈ys , m₃∈zs)
                   , (m₂ , m₃ , N.≤-refl , m₂∈ys , m₃∈zs)
                 (inj₂ l₃≤l₂) →
                     l₃ , m₂ N.+ m₃
                   , (begin
                        l₃ N.* (m₂ N.+ m₃)       ≡⟨ N.*-distribˡ-+ l₃ _ _ ⟩
                        l₃ N.* m₂ N.+ l₃ N.* m₃  ≤⟨ N.+-mono-≤ (N.*-mono-≤ l₃≤l₂ N.≤-refl) N.≤-refl ⟩
                        l₂ N.* m₂ N.+ l₃ N.* m₃  ≤⟨ N.+-mono-≤ l₂m₂≤l₁ l₃m₃≤m₁ ⟩
                        l₁ N.+ m₁                ≤⟨ l₁+m₁≤n ⟩
                        n                        ∎)
                   , l₃∈xs
                   , (m₂ , m₃ , N.≤-refl , m₂∈ys , m₃∈zs)
                   , (m₂ , m₃ , N.≤-refl , m₂∈ys , m₃∈zs))

        lemma₂ = λ n →
            (λ ( l₁ , m₁ , n≤l₁m₁ , l₁∈xs
               , _
               , (l₂ , m₂ , m₁≤l₂+m₂ , l₂∈ys , m₂∈zs)
               ) →
                 l₁ N.* l₂ , l₁ N.* m₂
               , (begin
                    n                        ≤⟨ n≤l₁m₁ ⟩
                    l₁ N.* m₁                ≤⟨ N.*-mono-≤ (N.≤-refl {x = l₁}) m₁≤l₂+m₂ ⟩
                    l₁ N.* (l₂ N.+ m₂)       ≡⟨ N.*-distribˡ-+ l₁ _ _ ⟩
                    l₁ N.* l₂ N.+ l₁ N.* m₂  ∎)
               , ( (l₁ , l₂ , N.≤-refl , l₁∈xs , l₂∈ys)
                 , (l₁ , l₂ , N.≤-refl , l₁∈xs , l₂∈ys)
                 )
               , ( (l₁ , m₂ , N.≤-refl , l₁∈xs , m₂∈zs)
                 , (l₁ , m₂ , N.≤-refl , l₁∈xs , m₂∈zs)
                 ))
          , (λ ( l₁ , m₁ , n≤l₁+m₁
               , ( _
                 , (l₂ , m₂ , l₁≤l₂m₂ , l₂∈xs , m₂∈ys)
                 )
               , ( _
                 , (l₃ , m₃ , m₁≤l₃m₃ , l₃∈xs , m₃∈zs)
                 )
               ) →
               case N.≤-total l₂ l₃ of λ where
                 (inj₁ l₂≤l₃) →
                     l₃ , m₂ N.+ m₃
                   , (begin
                        n                        ≤⟨ n≤l₁+m₁ ⟩
                        l₁ N.+ m₁                ≤⟨ N.+-mono-≤ l₁≤l₂m₂ m₁≤l₃m₃ ⟩
                        l₂ N.* m₂ N.+ l₃ N.* m₃  ≤⟨ N.+-mono-≤ (N.*-mono-≤ l₂≤l₃ N.≤-refl) N.≤-refl ⟩
                        l₃ N.* m₂ N.+ l₃ N.* m₃  ≡˘⟨ N.*-distribˡ-+ l₃ _ _ ⟩
                        l₃ N.* (m₂ N.+ m₃)       ∎)
                   , l₃∈xs
                   , (m₂ , m₃ , N.≤-refl , m₂∈ys , m₃∈zs)
                   , (m₂ , m₃ , N.≤-refl , m₂∈ys , m₃∈zs)
                 (inj₂ l₃≤l₂) →
                     l₂ , m₂ N.+ m₃
                   , (begin
                        n                        ≤⟨ n≤l₁+m₁ ⟩
                        l₁ N.+ m₁                ≤⟨ N.+-mono-≤ l₁≤l₂m₂ m₁≤l₃m₃ ⟩
                        l₂ N.* m₂ N.+ l₃ N.* m₃  ≤⟨ N.+-mono-≤ N.≤-refl (N.*-mono-≤ l₃≤l₂ N.≤-refl) ⟩
                        l₂ N.* m₂ N.+ l₂ N.* m₃  ≡˘⟨ N.*-distribˡ-+ l₂ _ _ ⟩
                        l₂ N.* (m₂ N.+ m₃)       ∎)
                   , l₂∈xs
                   , (m₂ , m₃ , N.≤-refl , m₂∈ys , m₃∈zs)
                   , (m₂ , m₃ , N.≤-refl , m₂∈ys , m₃∈zs))

    ----------------------------------------------------------------------
    -- Lemmas related to ℕ

    -- The set ℕ is a least one.

    ℕ-least : ℕ ≤ xs
    ℕ-least {xs = xs} = ≤⇔ ext .proj₂ λ n →
      n ∈ xs  →⟨ (λ _ → ∈ℕ) ⟩
      n ∈ ℕ   □

    opaque

      -- The natural number m is in ℕ · xs if and only if it is
      -- bounded by n₁n₂ for some natural numbers n₁ and n₂ where n₂
      -- is in xs.

      ∈ℕ·⇔ :
        m ∈ ℕ · xs ⇔
        (∃₂ λ n₁ n₂ → m N.≤ n₁ N.* n₂ × n₂ ∈ xs)
      ∈ℕ·⇔ {m} {xs} =
        m ∈ ℕ · xs                                                       ⇔⟨ ∈·⇔ ⟩
        Closure (λ m → ∃₂ λ n₁ n₂ → n₁ N.* n₂ ≡ m × n₁ ∈ ℕ × n₂ ∈ xs) m  ⇔⟨ (Closure-cong-⇔ λ m → Σ-cong-⇔ λ n₁ → Σ-cong-⇔ λ n₂ →
                                                                             id⇔ ×-cong-⇔ (proj₂ , (∈ℕ ,_))) ⟩
        Closure (λ m → ∃₂ λ n₁ n₂ → n₁ N.* n₂ ≡ m × n₂ ∈ xs) m           ⇔⟨ (λ { ( _ , _ , n₁n₂≤m , m≤n₃n₄
                                                                                 , (n₁ , n₂ , refl , n₂∈xs)
                                                                                 , (n₃ , n₄ , refl , n₄∈xs)
                                                                                 ) →
                                                                                 n₃ , n₄ , m≤n₃n₄ , n₄∈xs })
                                                                          , (λ (n₁ , n₂ , m≤n₁n₂ , n₂∈xs) →
                                                                                 0 , n₁ N.* n₂ , N.z≤n , m≤n₁n₂
                                                                               , (0  , n₂ , refl , n₂∈xs)
                                                                               , (n₁ , n₂ , refl , n₂∈xs))
                                                                          ⟩
        (∃₂ λ n₁ n₂ → m N.≤ n₁ N.* n₂ × n₂ ∈ xs)                         □⇔

    opaque

      -- The set ℕ · (xs + ys) is bounded by ℕ · ys.

      ℕ·+≤ℕ·ʳ : ℕ · (xs + ys) ≤ ℕ · ys
      ℕ·+≤ℕ·ʳ {xs} {ys} = ≤⇔ ext .proj₂ λ m →
        m ∈ ℕ · ys                                          ⇔⟨ ∈ℕ·⇔ ⟩→
        (∃₂ λ n₁ n₂ → m N.≤ n₁ N.* n₂ × n₂ ∈ ys)            →⟨ (λ (n₁ , n₂ , m≤n₁n₂ , n₂∈ys) →
                                                                  case non-empty of λ
                                                                    (n₃ , n₃∈xs) →
                                                                    n₁ , n₃ N.+ n₂
                                                                  , (begin
          m                                                            ≤⟨ m≤n₁n₂ ⟩
          n₁ N.* n₂                                                    ≤⟨ N.m≤n+m _ _ ⟩
          n₁ N.* n₃ N.+ n₁ N.* n₂                                      ≡˘⟨ N.*-distribˡ-+ n₁ _ _ ⟩
          n₁ N.* (n₃ N.+ n₂)                                           ∎)
                                                                  , (n₃ , n₂ , N.≤-refl , n₃∈xs , n₂∈ys)
                                                                  , (n₃ , n₂ , N.≤-refl , n₃∈xs , n₂∈ys)) ⟩
        (∃₂ λ n₁ n₂ → m N.≤ n₁ N.* n₂ × In N._+_ xs ys n₂)  ⇔⟨ (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → id⇔ ×-cong-⇔ sym⇔ ∈+⇔′) ⟩→
        (∃₂ λ n₁ n₂ → m N.≤ n₁ N.* n₂ × n₂ ∈ xs + ys)       ⇔⟨ sym⇔ ∈ℕ·⇔ ⟩→
        m ∈ ℕ · (xs + ys)                                   □
        where
        open N.≤-Reasoning

    --------------------------------------------------------------------
    -- Modalities

    open Graded.Modality S

    -- A "semiring with meet" for S.

    semiring-with-meet : Semiring-with-meet
    semiring-with-meet = record
      { _∧_     = _∪_
      ; _+_     = _+_
      ; _·_     = _·_
      ; 𝟘       = 𝟘
      ; 𝟙       = 𝟙
      ; ω       = ℕ
      ; ω≤𝟙     = ℕ-least
      ; ω·+≤ω·ʳ = ℕ·+≤ℕ·ʳ
      ; is-𝟘?   = λ xs → case is-𝟘? xs of λ where
          (inj₁ xs≡𝟘) → yes (xs≡𝟘 ext)
          (inj₂ xs≢𝟘) → no xs≢𝟘
      ; ∧-Semilattice = ∪-semilattice
      ; +-·-Semiring  = record
        { isSemiringWithoutAnnihilatingZero = record
           { +-isCommutativeMonoid = +-𝟘-commutative-monoid
           ; *-cong = cong₂ _·_
           ; *-assoc = ·-𝟙-commutative-monoid .IsCommutativeMonoid.isMonoid .IsMonoid.assoc
           ; *-identity = ·-𝟙-commutative-monoid .IsCommutativeMonoid.isMonoid .IsMonoid.identity
           ; distrib = ·-distrib-+
           }
        ; zero = ·-zero
        }
      ; +-distrib-∧ = +-distrib-∪
      ; ·-distrib-∧ = ·-distrib-∪
      }

    -- The "semiring with meet" has a well-behaved zero.

    has-well-behaved-zero : Has-well-behaved-zero semiring-with-meet
    has-well-behaved-zero = record
      { non-trivial  = 𝟙≢𝟘
      ; ∧-positiveˡ  = proj₁ ∘→ ∪-positive
      ; +-positiveˡ  = proj₁ ∘→ +-positive
      ; zero-product = zero-product
      }

    private
      module LB = LowerBounded semiring-with-meet ℕ (λ _ → ℕ-least)

    -- A natrec-star operator for S.
    --
    -- Other definitions might also work.

    has-star : Has-star semiring-with-meet
    has-star = LB.has-star

    -- A modality (of any kind) for S defined using the construction
    -- in Graded.Modality.Instances.BoundedStar.

    modality : Modality
    modality = LB.isModality
