------------------------------------------------------------------------
-- Non-empty sets of natural numbers
------------------------------------------------------------------------

-- These sets do not form modalities, but they satisfy quite a few
-- related properties (given certain assumptions). The only property
-- that is missing (if ω is defined to be 𝟙) is distributivity of
-- multiplication over addition. This property holds if equality is
-- replaced by inequality in a certain way, but if the definition of a
-- modality is changed so that only the weaker variant of
-- distributivity from this module is required, then it seems hard to
-- prove the substitution lemma in Graded.Substitution.Properties.

module Graded.Modality.Instances.Set.Non-empty where

import Tools.Algebra
open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Nat as N using (Nat; 1+)
open import Tools.Product
open import Tools.PropositionalEquality as PE
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum using (_⊎_; inj₁; inj₂)

open import Graded.Modality
import Graded.Modality.Instances.Set as Set

private variable
  a     : Level
  A S   : Set _
  P     : A → Set _
  xs ys : S
  m n   : Nat

-- A specification of non-empty sets of natural numbers with a
-- singleton operation.

record Is-non-empty-set-[] (S : Set a) : Set (lsuc (lsuc a)) where
  infix 10 _∈_

  field
    -- The membership relation.
    _∈_ : Nat → S → Set a

    -- An assumption used in the statement of →≡ (possibly function
    -- extensionality).
    Ext : Set (lsuc a)

    -- Two sets are equal if their membership relations are pointwise
    -- logically equivalent (assuming that Ext is inhabited).
    →≡ : Ext → (∀ n → n ∈ xs ⇔ n ∈ ys) → xs ≡ ys

    -- Every set is non-empty.
    non-empty : ∃ λ n → n ∈ xs

    -- Singleton sets.
    [_]  : Nat → S
    ∈[]⇔ : m ∈ [ n ] ⇔ m ≡ n

  ----------------------------------------------------------------------
  -- Some derived definitions

  -- If the type n ∉ xs is inhabited, then n is not a member of xs.

  infix 10 _∉_

  _∉_ : Nat → S → Set a
  n ∉ xs = ¬ n ∈ xs

  -- A set that contains exactly 0.

  𝟘 : S
  𝟘 = [ 0 ]

  -- A set that contains exactly 1.

  𝟙 : S
  𝟙 = [ 1 ]

  -- The property of containing exactly the given number.

  Contains-exactly : Nat → S → Set a
  Contains-exactly n xs = n ∈ xs × ∀ m → m ∈ xs → m ≡ n

  -- The property of having a non-zero member.

  Non-zero-member : S → Set a
  Non-zero-member xs = ∃ λ n → n ≢ 0 × n ∈ xs

  ----------------------------------------------------------------------
  -- Some lemmas related to Non-zero-member and Contains-exactly 0

  -- A set does not have a non-zero member if and only if it contains
  -- exactly 0.

  ¬Non-zero-member⇔ : (¬ Non-zero-member xs) ⇔ Contains-exactly 0 xs
  ¬Non-zero-member⇔ {xs = xs} =
      (λ hyp → 0∈ hyp , ∈→≡0 hyp)
    , (λ (_ , ∈→≡0) (n , n≢0 , n∈xs) →
         n≢0 (∈→≡0 n n∈xs))
    where
    module _ (not-non-zero : ¬ Non-zero-member xs) where

      ∈→≡0 : ∀ n → n ∈ xs → n ≡ 0
      ∈→≡0  0      _   = refl
      ∈→≡0  (1+ _) ∈xs = ⊥-elim $ not-non-zero (_ , (λ ()) , ∈xs)

      0∈ : 0 ∈ xs
      0∈ =
        case non-empty of λ {
          (_ , ∈xs) →
        subst (_∈ _) (∈→≡0 _ ∈xs) ∈xs }

  -- If a set does not contain exactly 0, then it does not not have a
  -- non-zero member.

  →¬¬Non-zero-member : ¬ Contains-exactly 0 xs → ¬ ¬ Non-zero-member xs
  →¬¬Non-zero-member = _∘→ ¬Non-zero-member⇔ .proj₁

  -- If neither xs nor ys contain exactly 0, then it is not the case
  -- that, for all pairs of elements m ∈ xs and n ∈ ys, m times n is
  -- zero (expressed in a somewhat roundabout way).

  multiplication-lemma :
    ¬ Contains-exactly 0 xs → ¬ Contains-exactly 0 ys →
    ¬ (∀ n → (∃₂ λ m₁ m₂ → m₁ N.* m₂ ≡ n × m₁ ∈ xs × m₂ ∈ ys) → n ≡ 0)
  multiplication-lemma {xs = xs} {ys = ys} xs-not-zero ys-not-zero =
    (∀ n → (∃₂ λ m₁ m₂ → m₁ N.* m₂ ≡ n × m₁ ∈ xs × m₂ ∈ ys) → n ≡ 0)  →⟨ (λ hyp _ _ m₁∈xs m₂∈ys →
                                                                            N.m*n≡0⇒m≡0∨n≡0 _ $
                                                                            hyp _ (_ , _ , refl , m₁∈xs , m₂∈ys)) ⟩

    (∀ m₁ m₂ → m₁ ∈ xs → m₂ ∈ ys → m₁ ≡ 0 ⊎ m₂ ≡ 0)                   →⟨ (λ hyp ((_ , m₁≢0 , m₁∈xs) , (_ , m₂≢0 , m₂∈ys)) →
                                                                            case hyp _ _ m₁∈xs m₂∈ys of λ where
                                                                              (inj₁ m₁≡0) → m₁≢0 m₁≡0
                                                                              (inj₂ m₂≡0) → m₂≢0 m₂≡0) ⟩

    ¬ (Non-zero-member xs × Non-zero-member ys)                       →⟨ (λ hyp →
                                                                            →¬¬Non-zero-member xs-not-zero λ xs-not-non-zero →
                                                                            →¬¬Non-zero-member ys-not-zero λ ys-not-non-zero →
                                                                            hyp (xs-not-non-zero , ys-not-non-zero)) ⟩
    ⊥                                                                 □

  ----------------------------------------------------------------------
  -- Some lemmas related to _∈_

  -- If two sets are equal, then their membership relations are
  -- pointwise logically equivalent.

  ≡→ : xs ≡ ys → ∀ n → n ∈ xs ⇔ n ∈ ys
  ≡→ refl _ = id⇔

  -- Two sets are equal if and only if their membership relations are
  -- pointwise logically equivalent (assuming that Ext is inhabited).

  ≡⇔ : Ext → xs ≡ ys ⇔ (∀ n → n ∈ xs ⇔ n ∈ ys)
  ≡⇔ ext = ≡→ , →≡ ext

  ----------------------------------------------------------------------
  -- Some lemmas related to [_]

  -- If the set xs is equal to [ n ], then xs contains exactly n.

  ≡[]→ : xs ≡ [ n ] → Contains-exactly n xs
  ≡[]→ refl = ∈[]⇔ .proj₂ refl , λ _ → ∈[]⇔ .proj₁

  -- If Ext is inhabited, then the set xs is equal to [ n ] if and
  -- only if xs contains exactly n.

  ≡[]⇔ : Ext → xs ≡ [ n ] ⇔ Contains-exactly n xs
  ≡[]⇔ {xs = xs} {n = n} ext =
    xs ≡ [ n ]                       ⇔⟨ ≡⇔ ext ⟩
    (∀ m → m ∈ xs ⇔ m ∈ [ n ])       ⇔⟨ (Π-cong-⇔ λ _ → id⇔ ⇔-cong-⇔ ∈[]⇔) ⟩
    (∀ m → m ∈ xs ⇔ m ≡ n)           ⇔⟨ Π⇔≡⇔ ⟩
    n ∈ xs × (∀ m → m ∈ xs → m ≡ n)  □⇔

  -- A variant of ≡[]⇔.

  ≡[]⇔′ :
    Ext →
    (∀ {m} → m ∈ xs ⇔ P m) →
    xs ≡ [ n ] ⇔ (P n × ∀ m → P m → m ≡ n)
  ≡[]⇔′ {xs = xs} {P = P} {n = n} ext hyp =
    xs ≡ [ n ]                       ⇔⟨ ≡[]⇔ ext ⟩
    n ∈ xs × (∀ m → m ∈ xs → m ≡ n)  ⇔⟨ hyp ×-cong-⇔ (Π-cong-⇔ λ _ → hyp →-cong-⇔ id⇔) ⟩
    P n × (∀ m → P m → m ≡ n)        □⇔

  -- 𝟙 is distinct from 𝟘.

  𝟙≢𝟘 : 𝟙 ≢ 𝟘
  𝟙≢𝟘 =
    𝟙 ≡ 𝟘  →⟨ proj₁ ∘→ ≡[]→ ⟩
    0 ∈ 𝟙  →⟨ ∈[]⇔ .proj₁ ⟩
    0 ≡ 1  →⟨ (λ ()) ⟩
    ⊥      □

-- A specification of non-empty sets of natural numbers with
-- singleton, union, addition and multiplication.
--
-- For an implementation, see
-- Graded.Modality.Instances.Set.Non-empty.Implementation.

record Is-non-empty-set (S : Set a) : Set (lsuc (lsuc a)) where
  field
    -- Is-non-empty-set S implies Is-non-empty-set-[] S.
    is-non-empty-set-[] : Is-non-empty-set-[] S

  open Is-non-empty-set-[] is-non-empty-set-[] public

  infixr 45 _·_
  infixr 40 _+_
  infixr 35 _∪_

  field
    -- Union.
    _∪_ : S → S → S
    ∈∪⇔ : n ∈ xs ∪ ys ⇔ (n ∈ xs ⊎ n ∈ ys)

    -- Addition.
    _+_ : S → S → S
    ∈+⇔ : n ∈ xs + ys ⇔ ∃₂ λ l m → l N.+ m ≡ n × l ∈ xs × m ∈ ys

    -- Multiplication.
    _·_ : S → S → S
    ∈·⇔ : n ∈ xs · ys ⇔ ∃₂ λ l m → l N.* m ≡ n × l ∈ xs × m ∈ ys

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
      (∀ n → n ∈ xs ⇔ n ∈ xs ∪ ys)  ⇔⟨ (Π-cong-⇔ λ _ →
                                          proj₂
                                        , (∈∪⇔ .proj₂ ∘→ inj₁ ,_)) ⟩

      (∀ n → n ∈ xs ∪ ys → n ∈ xs)  ⇔⟨ (Π-cong-⇔ λ n →
                                          (_∘→ ∈∪⇔ .proj₂ ∘→ inj₂)
                                        , (λ hyp →
        n ∈ xs ∪ ys                            ⇔⟨ ∈∪⇔ ⟩→
        n ∈ xs ⊎ n ∈ ys                        →⟨ (λ { (inj₁ ∈xs) → ∈xs; (inj₂ ∈ys) → hyp ∈ys }) ⟩
        n ∈ xs                                 □)) ⟩

      (∀ n → n ∈ ys → n ∈ xs)       □⇔

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
  -- Some negative results

  open Tools.Algebra S

  private
    module ∪-𝟙 =
      Set.∪-𝟙
        (record
           { _∈_ = _∈_
           ; _+_ = _+_
           ; ∈+⇔ = ∈+⇔
           ; _·_ = _·_
           ; ∈·⇔ = ∈·⇔
           })
        _∪_ ∈∪⇔ [ 1 ] ∈[]⇔

  -- Multiplication does not distribute from the left over addition for
  -- any instance of Is-non-empty-set.

  ¬-·-distribˡ-+ : ¬ _·_ DistributesOverˡ _+_
  ¬-·-distribˡ-+ = ∪-𝟙.¬-·-distribˡ-+

  -- Multiplication does not sub-distribute (in a certain sense) from
  -- the left over addition for any instance of Is-non-empty-set.
  --
  -- See also ·-sub-distrib-+ below.

  ¬-·-sub-distribˡ-+ : ¬ _·_ SubDistributesOverˡ _+_ by _≤_
  ¬-·-sub-distribˡ-+ = ∪-𝟙.¬-·-sub-distribˡ-+

  -- There is no "semiring with meet" for which the semiring's
  -- implementations of addition and multiplication match those of the
  -- set.

  no-semiring-with-meet :
    (semiring : Semiring-with-meet S) →
    Semiring-with-meet._+_ semiring ≡ _+_ →
    Semiring-with-meet._·_ semiring ≡ _·_ →
    ⊥
  no-semiring-with-meet = ∪-𝟙.no-semiring-with-meet

  -- There is no modality for which the modality's implementations of
  -- addition and multiplication match those of the set.

  no-modality :
    (modality : Modality S) →
    Modality._+_ modality ≡ _+_ →
    Modality._·_ modality ≡ _·_ →
    ⊥
  no-modality = ∪-𝟙.no-modality

  ----------------------------------------------------------------------
  -- Some positive results

  -- The following lemmas are proved under the assumption that Ext is
  -- inhabited.

  module _ (ext : Ext) where

    -- The following lemma is proved under the assumption that there
    -- is a set that contains every natural number.

    module ℕ (ℕ : S) (∈ℕ : ∀ {n} → n ∈ ℕ) where

      -- The set ℕ is a least one.

      ℕ-least : ℕ ≤ xs
      ℕ-least {xs = xs} = ≤⇔ ext .proj₂ λ n →
        n ∈ xs  →⟨ (λ _ → ∈ℕ) ⟩
        n ∈ ℕ   □

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
        n ∈ (xs ∪ ys) ∪ zs          ⇔⟨ (∈∪⇔ ⊎-cong-⇔ id⇔) ∘⇔ ∈∪⇔ ⟩
        (n ∈ xs ⊎ n ∈ ys) ⊎ n ∈ zs  ⇔⟨ ⊎-assoc-⇔ ⟩
        n ∈ xs ⊎ (n ∈ ys ⊎ n ∈ zs)  ⇔˘⟨ (id⇔ ⊎-cong-⇔ ∈∪⇔) ∘⇔ ∈∪⇔ ⟩
        n ∈ xs ∪ (ys ∪ zs)          □⇔

      ∪-idem : Idempotent _∪_
      ∪-idem xs = ≡⇔ ext .proj₂ λ n →
        n ∈ xs ∪ xs      ⇔⟨ ∈∪⇔ ⟩
        n ∈ xs ⊎ n ∈ xs  ⇔⟨ ⊎-idem-⇔ ⟩
        n ∈ xs           □⇔

      ∪-comm : Commutative _∪_
      ∪-comm xs ys = ≡⇔ ext .proj₂ λ n →
        n ∈ xs ∪ ys      ⇔⟨ ∈∪⇔ ⟩
        n ∈ xs ⊎ n ∈ ys  ⇔⟨ ⊎-comm-⇔ ⟩
        n ∈ ys ⊎ n ∈ xs  ⇔˘⟨ ∈∪⇔ ⟩
        n ∈ ys ∪ xs      □⇔

    open IsMeetSemilattice ∪-semilattice
      using () renaming (comm to ∪-comm)

    -- Union is positive.

    ∪-positive : xs ∪ ys ≡ 𝟘 → xs ≡ 𝟘 × ys ≡ 𝟘
    ∪-positive eq =
      ∪-positiveˡ eq , ∪-positiveˡ (trans (∪-comm _ _) eq)
      where
      ∪-positiveˡ : xs ∪ ys ≡ 𝟘 → xs ≡ 𝟘
      ∪-positiveˡ {xs = xs} {ys = ys} =
        xs ∪ ys ≡ 𝟘                                          ⇔⟨ ≡[]⇔′ ext ∈∪⇔ ⟩→
        (0 ∈ xs ⊎ 0 ∈ ys) × (∀ n → n ∈ xs ⊎ n ∈ ys → n ≡ 0)  →⟨ proj₂ ⟩
        (∀ n → n ∈ xs ⊎ n ∈ ys → n ≡ 0)                      →⟨ (λ hyp _ → hyp _ ∘→ inj₁) ⟩
        (∀ n → n ∈ xs → n ≡ 0)                               →⟨ (λ hyp → subst (_∈ _) (uncurry hyp non-empty) (non-empty .proj₂) , hyp) ⟩
        0 ∈ xs × (∀ n → n ∈ xs → n ≡ 0)                      ⇔˘⟨ ≡[]⇔ ext ⟩→
        xs ≡ 𝟘                                               □

    --------------------------------------------------------------------
    -- Lemmas for an arbitrary binary operator that satisfies a
    -- certain property

    module Operator
      {_∙_ : Nat → Nat → Nat}
      {ε : Nat}
      (∙-ε-commutative-monoid :
         Tools.Algebra.IsCommutativeMonoid Nat _∙_ ε)
      (_⊙_ : S → S → S)
      (∈⊙⇔ :
         ∀ {n xs ys} →
         n ∈ (xs ⊙ ys) ⇔ (∃₂ λ l m → (l ∙ m) ≡ n × l ∈ xs × m ∈ ys))
      where

      private
        module M =
          Tools.Algebra.IsCommutativeMonoid Nat ∙-ε-commutative-monoid

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
        open Tools.Reasoning.PropositionalEquality

        assoc : Associative _⊙_
        assoc xs ys zs = ≡⇔ ext .proj₂ λ n →
          n ∈ ((xs ⊙ ys) ⊙ zs)                                     ⇔⟨ ∈⊙⇔ ⟩

          (∃₂ λ m₁ m₂ → (m₁ ∙ m₂) ≡ n × m₁ ∈ (xs ⊙ ys) × m₂ ∈ zs)  ⇔⟨ (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ →
                                                                       ∈⊙⇔ ×-cong-⇔ id⇔) ⟩
          (∃₂ λ m₁ m₂ → (m₁ ∙ m₂) ≡ n ×
           (∃₂ λ m₃ m₄ → (m₃ ∙ m₄) ≡ m₁ × m₃ ∈ xs × m₄ ∈ ys) ×
           m₂ ∈ zs)                                                ⇔⟨ (λ { ( m₁ , m₂ , m₁⊙m₂≡n
                                                                           , (m₃ , m₄ , m₃⊙m₄≡m₁ , m₃∈xs , m₄∈ys)
                                                                           , m₂∈zs
                                                                           ) →
                                                                             m₃ , m₄ ∙ m₂
                                                                           , ((m₃ ∙ (m₄ ∙ m₂))  ≡˘⟨ M.assoc _ _ _ ⟩
                                                                              ((m₃ ∙ m₄) ∙ m₂)  ≡⟨ cong (_∙ _) m₃⊙m₄≡m₁ ⟩
                                                                              (m₁ ∙ m₂)         ≡⟨ m₁⊙m₂≡n ⟩
                                                                              n                 ∎)
                                                                           , m₃∈xs , m₄ , m₂ , refl , m₄∈ys , m₂∈zs })
                                                                    , (λ { ( m₁ , m₂ , m₁⊙m₂≡n , m₁∈xs
                                                                           , m₃ , m₄ , m₃⊙m₄≡m₂ , m₃∈ys , m₄∈zs
                                                                           ) →
                                                                             m₁ ∙ m₃ , m₄
                                                                           , (((m₁ ∙ m₃) ∙ m₄)  ≡⟨ M.assoc _ _ _ ⟩
                                                                              (m₁ ∙ (m₃ ∙ m₄))  ≡⟨ cong (_ ∙_) m₃⊙m₄≡m₂ ⟩
                                                                              (m₁ ∙ m₂)         ≡⟨ m₁⊙m₂≡n ⟩
                                                                              n                 ∎)
                                                                           , (m₁ , m₃ , refl , m₁∈xs , m₃∈ys) , m₄∈zs })
                                                                    ⟩
          (∃₂ λ m₁ m₂ → (m₁ ∙ m₂) ≡ n × m₁ ∈ xs ×
           ∃₂ λ m₃ m₄ → (m₃ ∙ m₄) ≡ m₂ × m₃ ∈ ys × m₄ ∈ zs)        ⇔˘⟨ (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ →
                                                                        ∈⊙⇔) ⟩

          (∃₂ λ m₁ m₂ → (m₁ ∙ m₂) ≡ n × m₁ ∈ xs × m₂ ∈ (ys ⊙ zs))  ⇔˘⟨ ∈⊙⇔ ⟩

          n ∈ (xs ⊙ (ys ⊙ zs))                                     □⇔

        comm : Commutative _⊙_
        comm xs ys = ≡⇔ ext .proj₂ λ n →
          n ∈ (xs ⊙ ys)                                     ⇔⟨ ∈⊙⇔ ⟩
          (∃₂ λ m₁ m₂ → (m₁ ∙ m₂) ≡ n × m₁ ∈ xs × m₂ ∈ ys)  ⇔⟨ (λ { (m₁ , m₂ , refl , m₁∈xs , m₂∈ys) →
                                                                    m₂ , m₁ , M.comm _ _ , m₂∈ys , m₁∈xs })
                                                             , (λ { (m₁ , m₂ , refl , m₁∈ys , m₂∈xs) →
                                                                    m₂ , m₁ , M.comm _ _ , m₂∈xs , m₁∈ys })
                                                             ⟩
          (∃₂ λ m₁ m₂ → (m₁ ∙ m₂) ≡ n × m₁ ∈ ys × m₂ ∈ xs)  ⇔˘⟨ ∈⊙⇔ ⟩
          n ∈ (ys ⊙ xs)                                     □⇔

        identityˡ : LeftIdentity [ ε ] _⊙_
        identityˡ xs = ≡⇔ ext .proj₂ λ n →
          n ∈ ([ ε ] ⊙ xs)                                     ⇔⟨ ∈⊙⇔ ⟩
          (∃₂ λ m₁ m₂ → (m₁ ∙ m₂) ≡ n × m₁ ∈ [ ε ] × m₂ ∈ xs)  ⇔⟨ (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ →
                                                               ∈[]⇔ ×-cong-⇔ id⇔) ⟩
          (∃₂ λ m₁ m₂ → (m₁ ∙ m₂) ≡ n × m₁ ≡ ε × m₂ ∈ xs)      ⇔⟨ (λ { (.ε , n , refl , refl , n∈xs) →
                                                                       subst (_∈ _) (sym (M.identityˡ _)) n∈xs })
                                                                , (λ n∈xs → ε , n , M.identityˡ _ , refl , n∈xs)
                                                                ⟩
          n ∈ xs                                               □⇔

        identity : Identity [ ε ] _⊙_
        identity = identityˡ , comm+idˡ⇒idʳ comm identityˡ

      -- The binary operator _⊙_ distributes over _∪_.

      distrib-∪ : _⊙_ DistributesOver _∪_
      distrib-∪ =
          distribˡ-∪
        , comm+distrˡ⇒distrʳ
            (IsCommutativeMonoid.comm commutative-monoid)
            distribˡ-∪
        where
        distribˡ-∪ : _⊙_ DistributesOverˡ _∪_
        distribˡ-∪ xs ys zs = ≡⇔ ext .proj₂ λ n →
          n ∈ (xs ⊙ (ys ∪ zs))                                          ⇔⟨ ∈⊙⇔ ⟩

          (∃₂ λ m₁ m₂ → (m₁ ∙ m₂) ≡ n × m₁ ∈ xs × m₂ ∈ ys ∪ zs)         ⇔⟨ (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ →
                                                                            ∈∪⇔) ⟩

          (∃₂ λ m₁ m₂ → (m₁ ∙ m₂) ≡ n × m₁ ∈ xs × (m₂ ∈ ys ⊎ m₂ ∈ zs))  ⇔⟨ (λ where
                                                                              (m₁ , m₂ , m₁⊙m₂≡n , m₁∈xs , inj₁ m₂∈ys) →
                                                                                inj₁ (m₁ , m₂ , m₁⊙m₂≡n , m₁∈xs , m₂∈ys)
                                                                              (m₁ , m₂ , m₁⊙m₂≡n , m₁∈xs , inj₂ m₂∈zs) →
                                                                                inj₂ (m₁ , m₂ , m₁⊙m₂≡n , m₁∈xs , m₂∈zs))
                                                                         , (λ where
                                                                              (inj₁ (m₁ , m₂ , m₁⊙m₂≡n , m₁∈xs , m₂∈ys)) →
                                                                                m₁ , m₂ , m₁⊙m₂≡n , m₁∈xs , inj₁ m₂∈ys
                                                                              (inj₂ (m₁ , m₂ , m₁⊙m₂≡n , m₁∈xs , m₂∈zs)) →
                                                                                m₁ , m₂ , m₁⊙m₂≡n , m₁∈xs , inj₂ m₂∈zs)
                                                                         ⟩
          (∃₂ λ m₁ m₂ → (m₁ ∙ m₂) ≡ n × m₁ ∈ xs × m₂ ∈ ys) ⊎
          (∃₂ λ m₁ m₂ → (m₁ ∙ m₂) ≡ n × m₁ ∈ xs × m₂ ∈ zs)              ⇔˘⟨ ∈⊙⇔ ⊎-cong-⇔ ∈⊙⇔ ⟩

          n ∈ (xs ⊙ ys) ⊎ n ∈ (xs ⊙ zs)                                 ⇔˘⟨ ∈∪⇔ ⟩

          n ∈ (xs ⊙ ys) ∪ (xs ⊙ zs)                                     □⇔

    --------------------------------------------------------------------
    -- Lemmas related to _+_

    private
      module Addition =
        Operator N.+-0-isCommutativeMonoid _+_ ∈+⇔

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
      +-positiveˡ : xs + ys ≡ 𝟘 → xs ≡ 𝟘
      +-positiveˡ {xs = xs} {ys = ys} =
        xs + ys ≡ 𝟘                                                       ⇔⟨ ≡[]⇔′ ext ∈+⇔ ⟩→

        (∃₂ λ m₁ m₂ → m₁ N.+ m₂ ≡ 0 × m₁ ∈ xs × m₂ ∈ ys) ×
        (∀ n → (∃₂ λ m₁ m₂ → m₁ N.+ m₂ ≡ n × m₁ ∈ xs × m₂ ∈ ys) → n ≡ 0)  →⟨ (λ { ((0 , _ , refl , 0∈xs , 0∈ys) , hyp) →
                                                                                    0∈xs
                                                                                  , (λ _ ∈xs →
                                                                                       hyp _ (_ , _ , N.+-identityʳ _ , ∈xs , 0∈ys)) }) ⟩

        0 ∈ xs × (∀ n → n ∈ xs → n ≡ 0)                                   ⇔˘⟨ ≡[]⇔ ext ⟩→

        xs ≡ 𝟘                                                            □

    --------------------------------------------------------------------
    -- Lemmas related to _·_

    private
      module Multiplication =
        Operator N.*-1-isCommutativeMonoid _·_ ∈·⇔

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
    ·-zero = ·-zeroˡ , comm+zeˡ⇒zeʳ ·-comm ·-zeroˡ
      where
      ·-zeroˡ : LeftZero 𝟘 _·_
      ·-zeroˡ xs = ≡⇔ ext .proj₂ λ n →
        n ∈ 𝟘 · xs                                       ⇔⟨ ∈·⇔ ⟩
        (∃₂ λ m₁ m₂ → m₁ N.* m₂ ≡ n × m₁ ∈ 𝟘 × m₂ ∈ xs)  ⇔⟨ (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ →
                                                             ∈[]⇔ ×-cong-⇔ id⇔) ⟩
        (∃₂ λ m₁ m₂ → m₁ N.* m₂ ≡ n × m₁ ≡ 0 × m₂ ∈ xs)  ⇔⟨ (λ { (_ , _ , refl , refl , _) → refl })
                                                          , (λ { refl → 0 , non-empty .proj₁ , refl , refl , non-empty .proj₂ })
                                                          ⟩
        n ≡ 0                                            ⇔˘⟨ ∈[]⇔ ⟩
        n ∈ 𝟘                                            □⇔

    -- The following result is proved under the assumption that
    -- equality with 𝟘 is decidable (modulo an Ext assumption for the
    -- "yes" case).

    module Is-𝟘? (is-𝟘? : ∀ xs → (Ext → xs ≡ 𝟘) ⊎ xs ≢ 𝟘) where

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
          xs · ys ≡ 𝟘                                                →⟨ ≡[]→ ⟩

          0 ∈ xs · ys × (∀ n → n ∈ xs · ys → n ≡ 0)                  →⟨ proj₂ ⟩

          (∀ n → n ∈ xs · ys → n ≡ 0)                                ⇔⟨ (Π-cong-⇔ λ _ → ∈·⇔ →-cong-⇔ id⇔) ⟩→

          (∀ n → (∃₂ λ m₁ m₂ → m₁ N.* m₂ ≡ n × m₁ ∈ xs × m₂ ∈ ys) →
           n ≡ 0)                                                    →⟨ multiplication-lemma
                                                                          (xs≢𝟘 ∘→ ≡[]⇔ ext .proj₂)
                                                                          (ys≢𝟘 ∘→ ≡[]⇔ ext .proj₂) ⟩

          ⊥                                                          →⟨ ⊥-elim ⟩

          xs ≡ 𝟘 ⊎ ys ≡ 𝟘                                            □

    --------------------------------------------------------------------
    -- Another distributivity law

    -- Multiplication sub-distributes (in a certain sense) over
    -- addition.
    --
    -- See also ¬-·-distribˡ-+ and ¬-·-sub-distribˡ-+ above.

    ·-sub-distrib-+ : _·_ SubDistributesOver _+_ by flip _≤_
    ·-sub-distrib-+ =
        ·-sub-distribˡ-+
      , (λ xs ys zs →                          $⟨ ·-sub-distribˡ-+ _ _ _ ⟩
           xs · ys + xs · zs ≤ xs · (ys + zs)  ≡⟨ cong₂ _≤_ (cong₂ _+_ (·-comm _ _) (·-comm _ _)) (·-comm _ _) ⟩→
           ys · xs + zs · xs ≤ (ys + zs) · xs  □)
      where
      ·-sub-distribˡ-+ : _·_ SubDistributesOverˡ _+_ by flip _≤_
      ·-sub-distribˡ-+ xs ys zs = ≤⇔ ext .proj₂ λ n →
        n ∈ xs · (ys + zs)                                          ⇔⟨ ∈·⇔ ⟩→

        (∃₂ λ m₁ m₂ → m₁ N.* m₂ ≡ n × m₁ ∈ xs × m₂ ∈ ys + zs)       ⇔⟨ (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ →
                                                                        ∈+⇔) ⟩→
        (∃₂ λ m₁ m₂ → m₁ N.* m₂ ≡ n × m₁ ∈ xs ×
         ∃₂ λ m₃ m₄ → m₃ N.+ m₄ ≡ m₂ × m₃ ∈ ys × m₄ ∈ zs)           →⟨ (λ (m₁ , m₂ , m₁m₂≡n , m₁∈xs , m₃ , m₄ , m₃+m₄≡m₂ , m₃∈ys , m₄∈zs) →
                                                                            m₁ N.* m₃
                                                                          , m₁ N.* m₄
                                                                          , (m₁ N.* m₃ N.+ m₁ N.* m₄  ≡˘⟨ N.*-distribˡ-+ m₁ _ _ ⟩
                                                                             m₁ N.* (m₃ N.+ m₄)       ≡⟨ cong (m₁ N.*_) m₃+m₄≡m₂ ⟩
                                                                             m₁ N.* m₂                ≡⟨ m₁m₂≡n ⟩
                                                                             n                        ∎)
                                                                          , (m₁ , m₃ , refl , m₁∈xs , m₃∈ys)
                                                                          , (m₁ , m₄ , refl , m₁∈xs , m₄∈zs))
                                                                     ⟩
        (∃₂ λ m₁ m₂ → m₁ N.+ m₂ ≡ n ×
         (∃₂ λ m₃ m₄ → m₃ N.* m₄ ≡ m₁ × m₃ ∈ xs × m₄ ∈ ys) ×
         (∃₂ λ m₅ m₆ → m₅ N.* m₆ ≡ m₂ × m₅ ∈ xs × m₆ ∈ zs))         ⇔˘⟨ (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ →
                                                                         ∈·⇔ ×-cong-⇔ ∈·⇔) ⟩→

        (∃₂ λ m₁ m₂ → m₁ N.+ m₂ ≡ n × m₁ ∈ xs · ys × m₂ ∈ xs · zs)  ⇔˘⟨ ∈+⇔ ⟩→

        n ∈ xs · ys + xs · zs                                       □
        where
        open Tools.Reasoning.PropositionalEquality
