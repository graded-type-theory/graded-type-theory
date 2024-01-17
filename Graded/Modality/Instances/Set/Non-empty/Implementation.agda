------------------------------------------------------------------------
-- An implementation of the set interface in
-- Graded.Modality.Instances.Set.Non-empty
------------------------------------------------------------------------

module Graded.Modality.Instances.Set.Non-empty.Implementation where

open import Tools.Bool
open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Nat as ℕ using (Nat; 1+)
open import Tools.Product as Σ
open import Tools.PropositionalEquality
open import Tools.Relation
open import Tools.Sum as ⊎ using (_⊎_; inj₁; inj₂)
open import Tools.Unit

open import Graded.Modality.Instances.Set.Non-empty
  using (Is-non-empty-set-[]; Is-non-empty-set)

private variable
  m n : Nat
  p   : Nat → Bool
  f   : Nat → Nat → Nat

------------------------------------------------------------------------
-- The type

-- The property of being non-empty (sometimes true).
--
-- The property is defined in such a way that, given function
-- extensionality, one can prove that it is propositional.

Non-empty : (Nat → Bool) → Set
Non-empty p = ℕ.∃-least (λ n → T (p n))

-- The property of either containing only 0, or not containing only 0.

Contains-only-0? : (Nat → Bool) → Set
Contains-only-0? p = Dec (∀ n → T (p n) → n ≡ 0)

-- Non-empty sets of natural numbers with decidable membership
-- predicates and (assuming function extensionality) decidable
-- equality with 𝟘.

Set-ℕ : Set
Set-ℕ = ∃ λ (p : Nat → Bool) → Non-empty p × Contains-only-0? p

private variable
  xs ys : Set-ℕ

------------------------------------------------------------------------
-- Some basic definitions

-- The membership predicate.

member? : Set-ℕ → Nat → Bool
member? = proj₁

-- The membership relation.

infix 10 _∈_

_∈_ : Nat → Set-ℕ → Set
n ∈ xs = T (member? xs n)

-- The membership relation is decidable.

infix 10 _∈?_

_∈?_ : ∀ n xs → Dec (n ∈ xs)
n ∈? xs with member? xs n
… | true  = yes _
… | false = no idᶠ

-- Sets are non-empty.

non-empty : ∀ xs → ∃ λ n → n ∈ xs
non-empty (_ , (_ , ∈xs , _) , _) = _ , ∈xs

-- Does the set only contain 0?

contains-only-0? : ∀ xs → Contains-only-0? (member? xs)
contains-only-0? (_ , _ , p) = p

-- For a non-empty predicate p the statements "p contains exactly 0"
-- and "p only contains 0" are logically equivalent.

Non-empty→Contains-exactly-0⇔Contains-only-0 :
  Non-empty p →
  (∀ n → T (p n) ⇔ n ≡ 0) ⇔ (∀ n → T (p n) → n ≡ 0)
Non-empty→Contains-exactly-0⇔Contains-only-0 {p = p} (m , m∈ , _) =
  ( (λ f n → f n .proj₁)
  , (λ f n →
         f n
       , λ { refl →   $⟨ m∈ ⟩
             T (p m)  →⟨ subst (T ∘→ p) (f m m∈) ⟩
             T (p 0)  □ })
  )

-- A constructor for Set-ℕ.

set :
  (p : Nat → Bool) →
  (∃ λ n → T (p n)) →
  (∀ n → T (p n) → n ≡ 0) ⊎ ¬ (∀ n → T (p n) ⇔ n ≡ 0) →
  Set-ℕ
set p non-empty is-𝟘? =
    p
  , non-empty′
  , (case is-𝟘? of λ where
       (inj₁ is-𝟘)     → yes is-𝟘
       (inj₂ is-not-𝟘) → no $
         (Non-empty→Contains-exactly-0⇔Contains-only-0 non-empty′
            →-cong-⇔
          id⇔)
           .proj₁
           is-not-𝟘)
  where
  non-empty′ = ℕ.∃⇔∃-least .proj₁ non-empty

------------------------------------------------------------------------
-- The set ℕ

-- The set containing all numbers.

ℕ : Set-ℕ
ℕ = set
  (λ _ → true)
  (0 , _)
  (inj₂
     ((∀ n → ⊤ ⇔ n ≡ 0)  →⟨ (λ hyp → hyp 1 .proj₁ _) ⟩
      1 ≡ 0              →⟨ (λ ()) ⟩
      ⊥                  □))

-- ℕ is correctly defined.

∈ℕ : ∀ n → n ∈ ℕ
∈ℕ = _

------------------------------------------------------------------------
-- Union

-- Union.

infixr 35 _∪_

_∪_ : Set-ℕ → Set-ℕ → Set-ℕ
xs ∪ ys = set
  mem?
  (                           $⟨ non-empty xs ⟩
   (∃ λ n → n ∈ xs)           →⟨ Σ.map idᶠ inj₁ ⟩
   (∃ λ n → n ∈ xs ⊎ n ∈ ys)  ⇔˘⟨ (Σ-cong-⇔ λ _ → T-∨) ⟩→
   (∃ λ n → T (mem? n))       □)
  (case contains-only-0? xs of λ where
     (no xs-is-not-𝟘) → inj₂
       ((∀ n → T (mem? n) ⇔ n ≡ 0)         ⇔⟨ (Π-cong-⇔ λ _ → T-∨ ⇔-cong-⇔ id⇔) ⟩→
        (∀ n → (n ∈ xs ⊎ n ∈ ys) ⇔ n ≡ 0)  →⟨ (λ hyp _ ∈xs → hyp _ .proj₁ (inj₁ ∈xs)) ⟩
        (∀ n → n ∈ xs → n ≡ 0)             →⟨ xs-is-not-𝟘 ⟩
        ⊥                                  □)
     (yes xs-is-𝟘) → case contains-only-0? ys of λ where
       (no ys-is-not-𝟘) → inj₂
         ((∀ n → T (mem? n) ⇔ n ≡ 0)         ⇔⟨ (Π-cong-⇔ λ _ → T-∨ ⇔-cong-⇔ id⇔) ⟩→
          (∀ n → (n ∈ xs ⊎ n ∈ ys) ⇔ n ≡ 0)  →⟨ (λ hyp _ ∈ys → hyp _ .proj₁ (inj₂ ∈ys)) ⟩
          (∀ n → n ∈ ys → n ≡ 0)             →⟨ ys-is-not-𝟘 ⟩
          ⊥                                  □)
       (yes ys-is-𝟘) → inj₁ λ n →
         T (mem? n)       ⇔⟨ T-∨ ⟩→
         n ∈ xs ⊎ n ∈ ys  →⟨ ⊎.map (xs-is-𝟘 _) (ys-is-𝟘 _) ⟩
         n ≡ 0 ⊎ n ≡ 0    ⇔⟨ ⊎-idem-⇔ ⟩→
         n ≡ 0            □)
  where
  mem? : Nat → Bool
  mem? = λ n → member? xs n ∨ member? ys n

-- Union is correctly defined.

∈∪⇔ : ∀ xs ys → n ∈ xs ∪ ys ⇔ (n ∈ xs ⊎ n ∈ ys)
∈∪⇔ _ _ = T-∨

------------------------------------------------------------------------
-- Extensionality

-- The following lemmas are proved under the assumption that function
-- extensionality holds.

module _ (fe : Function-extensionality lzero lzero) where

  -- The type Non-empty p is a proposition.

  Non-empty-propositional : Is-proposition (Non-empty p)
  Non-empty-propositional =
    ℕ.∃-least-propositional fe fe (λ _ → T-propositional)

  -- The type Contains-only-0? p is a proposition.

  Contains-only-0?-propositional :
    Is-proposition (Contains-only-0? p)
  Contains-only-0?-propositional =
    Is-proposition-Dec fe $
    Is-proposition-Π fe λ _ →
    Is-proposition-Π fe λ _ →
    ℕ.Nat-set

  -- Two sets are equal if their membership relations are
  -- pointwise logically equivalent.

  →≡ : (∀ n → n ∈ xs ⇔ n ∈ ys) → xs ≡ ys
  →≡ {xs = xs} {ys = ys} =
    (∀ n → n ∈ xs ⇔ n ∈ ys)                      ⇔⟨ id⇔ ⟩→
    (∀ n → T (member? xs n) ⇔ T (member? ys n))  ⇔⟨ (Π-cong-⇔ λ _ → T⇔T) ⟩→
    (∀ n → member? xs n ≡ member? ys n)          →⟨ (λ hyp →
                                                       case ext fe hyp of λ {
                                                         refl →
                                                       cong₂ (λ ne cez → member? xs , ne , cez)
                                                         Non-empty-propositional
                                                         Contains-only-0?-propositional })
                                                  ⟩
    xs ≡ ys                                      □

------------------------------------------------------------------------
-- Singleton sets

-- Singleton sets.

[_] : Nat → Set-ℕ
[_] = λ n → set (ℕ._== n) (n , rfl n) (is-0? n)
  where
  rfl : ∀ n → T (n ℕ.== n)
  rfl n = ℕ.T-== {m = n} .proj₂ refl

  is-0? :
    ∀ n → (∀ m → T (m ℕ.== n) → m ≡ 0) ⊎ ¬ (∀ m → T (m ℕ.== n) ⇔ m ≡ 0)
  is-0? 0 = inj₁ λ n →
    T (n ℕ.== 0)  ⇔⟨ ℕ.T-== ⟩→
    n ≡ 0         □
  is-0? n@(1+ _) = inj₂
    ((∀ m → T (m ℕ.== n) ⇔ m ≡ 0)  →⟨ proj₁ ∘→ (_$ _) ⟩
     (T (n ℕ.== n) → n ≡ 0)        →⟨ _$ rfl n ⟩
     n ≡ 0                         →⟨ (λ ()) ⟩
     ⊥                             □)

-- [_] is correctly defined.

∈[]⇔ : m ∈ [ n ] ⇔ m ≡ n
∈[]⇔ {m = m} {n = n} =
  T (m ℕ.== n)  ⇔⟨ ℕ.T-== ⟩
  m ≡ n         □⇔

-- There is an instance of Is-non-empty-set-[] for Set-ℕ.

is-non-empty-set-[] : Is-non-empty-set-[] Set-ℕ
is-non-empty-set-[] = λ where
  .Is-non-empty-set-[]._∈_ →
    _∈_
  .Is-non-empty-set-[].Ext →
    Function-extensionality lzero lzero
  .Is-non-empty-set-[].→≡ fe →
    →≡ fe
  .Is-non-empty-set-[].non-empty {xs = xs} →
    non-empty xs
  .Is-non-empty-set-[].[_] →
    [_]
  .Is-non-empty-set-[].∈[]⇔ →
    ∈[]⇔

private module Set-[] = Is-non-empty-set-[] is-non-empty-set-[]

-- Equality with [ 0 ] is decidable (modulo an assumption of function
-- extensionality for the "yes" case).

is-𝟘? :
  ∀ xs → (Function-extensionality lzero lzero → xs ≡ [ 0 ]) ⊎ xs ≢ [ 0 ]
is-𝟘? xs@(p , non-empty , is-𝟘?) = case is-𝟘? of λ where
    (yes is-𝟘) → inj₁ λ fe →       $⟨ is-𝟘 ⟩
      (∀ n → T (p n) → n ≡ 0)      ⇔˘⟨ lemma ⟩→
      (∀ n → T (p n) ⇔ n ∈ [ 0 ])  ⇔˘⟨ Set-[].≡⇔ (fe {_}) ⟩→
      xs ≡ [ 0 ]                   □
    (no is-not-𝟘) → inj₂
      (xs ≡ [ 0 ]                   →⟨ Set-[].≡→ ⟩
       (∀ n → T (p n) ⇔ n ∈ [ 0 ])  ⇔⟨ lemma ⟩→
       (∀ n → T (p n) → n ≡ 0)      →⟨ is-not-𝟘 ⟩
       ⊥                            □)
  where
  lemma =
    (∀ n → T (p n) ⇔ n ∈ [ 0 ])  ⇔⟨ (Π-cong-⇔ λ _ → id⇔ ⇔-cong-⇔ ∈[]⇔) ⟩
    (∀ n → T (p n) ⇔ n ≡ 0)      ⇔⟨ Non-empty→Contains-exactly-0⇔Contains-only-0 non-empty ⟩
    (∀ n → T (p n) → n ≡ 0)      □⇔

------------------------------------------------------------------------
-- Addition

-- Some lemmas used to implement addition.

private module Addition (xs ys : Set-ℕ) where

  -- A lemma used for both addition and multiplication.

  bin-op-lemma :
    T (ℕ.∃≤ n λ m₁ → ℕ.∃≤ n λ m₂ →
       (f m₁ m₂ ℕ.== n) ∧ member? xs m₁ ∧ member? ys m₂) ⇔
    (∃ λ m₁ → m₁ ℕ.≤ n × ∃ λ m₂ → m₂ ℕ.≤ n ×
     f m₁ m₂ ≡ n × m₁ ∈ xs × m₂ ∈ ys)
  bin-op-lemma =
    (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ →
     (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ →
      (ℕ.T-== ×-cong-⇔ T-∧) ∘⇔
      T-∧) ∘⇔
     ℕ.∃≤⇔) ∘⇔
    ℕ.∃≤⇔

  -- The membership predicate used for addition.

  ∈+? : Nat → Bool
  ∈+? n =
    ℕ.∃≤ n λ m₁ →
    ℕ.∃≤ n λ m₂ →
      (m₁ ℕ.+ m₂ ℕ.== n) ∧ member? xs m₁ ∧ member? ys m₂

  -- The correctness property for addition.

  ∈+⇔ : T (∈+? n) ⇔ ∃₂ λ m₁ m₂ → m₁ ℕ.+ m₂ ≡ n × m₁ ∈ xs × m₂ ∈ ys
  ∈+⇔ {n = n} =
    T (∈+? n)                                         ⇔⟨ bin-op-lemma ⟩

    (∃ λ m₁ → m₁ ℕ.≤ n × ∃ λ m₂ → m₂ ℕ.≤ n ×
     m₁ ℕ.+ m₂ ≡ n × m₁ ∈ xs × m₂ ∈ ys)               ⇔⟨ (λ (m₁ , _ , m₂ , _ , m₁+m₂≡n , m₁∈xs , m₂∈ys) →
                                                            m₁ , m₂ , m₁+m₂≡n , m₁∈xs , m₂∈ys)
                                                       , (λ (m₁ , m₂ , m₁+m₂≡n , m₁∈xs , m₂∈ys) →
                                                              m₁
                                                            , (begin
                                                                 m₁         ≤⟨ ℕ.m≤m+n _ _ ⟩
                                                                 m₁ ℕ.+ m₂  ≡⟨ m₁+m₂≡n ⟩
                                                                 n          ∎)
                                                            , m₂
                                                            , (begin
                                                                 m₂         ≤⟨ ℕ.m≤n+m _ _ ⟩
                                                                 m₁ ℕ.+ m₂  ≡⟨ m₁+m₂≡n ⟩
                                                                 n          ∎)
                                                            , m₁+m₂≡n
                                                            , m₁∈xs
                                                            , m₂∈ys)
                                                       ⟩

    (∃₂ λ m₁ m₂ → m₁ ℕ.+ m₂ ≡ n × m₁ ∈ xs × m₂ ∈ ys)  □⇔
    where
    open ℕ.≤-Reasoning

-- Addition.

infixr 40 _+_

_+_ : Set-ℕ → Set-ℕ → Set-ℕ
xs + ys = set
  ∈+?
  (                                                    $⟨ _ , _ , _ , refl , non-empty xs .proj₂ , non-empty ys .proj₂ ⟩
   (∃₃ λ n m₁ m₂ → m₁ ℕ.+ m₂ ≡ n × m₁ ∈ xs × m₂ ∈ ys)  ⇔˘⟨ (Σ-cong-⇔ λ _ → ∈+⇔) ⟩→
   (∃ λ n → T (∈+? n))                                 □)
  (case contains-only-0? xs of λ where
     (no xs-is-not-𝟘) → inj₂
       ((∀ n → T (∈+? n) ⇔ n ≡ 0)                                         →⟨ lemma ⟩

        (0 ∈ xs × 0 ∈ ys) ×
        (∀ n → (∃₂ λ m₁ m₂ → m₁ ℕ.+ m₂ ≡ n × m₁ ∈ xs × m₂ ∈ ys) → n ≡ 0)  →⟨ (λ ((_ , 0∈ys) , hyp) n n∈xs →
                                                                                hyp _ (n , 0 , ℕ.+-identityʳ _ , n∈xs , 0∈ys)) ⟩

        (∀ n → n ∈ xs → n ≡ 0)                                            →⟨ xs-is-not-𝟘 ⟩

        ⊥                                                                 □)
     (yes xs-is-𝟘) → case contains-only-0? ys of λ where
       (no ys-is-not-𝟘) → inj₂
         ((∀ n → T (∈+? n) ⇔ n ≡ 0)                                   →⟨ lemma ⟩

          (0 ∈ xs × 0 ∈ ys) ×
          (∀ n → (∃₂ λ m₁ m₂ → m₁ ℕ.+ m₂ ≡ n × m₁ ∈ xs × m₂ ∈ ys) →
           n ≡ 0)                                                     →⟨ (λ ((0∈xs , _) , hyp) n n∈ys →
                                                                            hyp _ (0 , n , refl , 0∈xs , n∈ys)) ⟩

          (∀ n → n ∈ ys → n ≡ 0)                                      →⟨ ys-is-not-𝟘 ⟩

          ⊥                                                           □)
       (yes ys-is-𝟘) → inj₁ λ n →
         T (∈+? n)                                         ⇔⟨ ∈+⇔ ⟩→
         (∃₂ λ m₁ m₂ → m₁ ℕ.+ m₂ ≡ n × m₁ ∈ xs × m₂ ∈ ys)  →⟨ (λ { (_ , _ , refl , m₁∈xs , m₂∈ys) →
                                                                   cong₂ ℕ._+_ (xs-is-𝟘 _ m₁∈xs) (ys-is-𝟘 _ m₂∈ys) }) ⟩
         n ≡ 0                                             □)
  where
  open Addition xs ys

  lemma =
    (∀ n → T (∈+? n) ⇔ n ≡ 0)                                   ⇔⟨ (Π-cong-⇔ λ _ → ∈+⇔ ⇔-cong-⇔ id⇔) ⟩→

    (∀ n →
     (∃₂ λ m₁ m₂ → m₁ ℕ.+ m₂ ≡ n × m₁ ∈ xs × m₂ ∈ ys) ⇔ n ≡ 0)  ⇔⟨ Π⇔≡⇔ ⟩→

    (∃₂ λ m₁ m₂ → m₁ ℕ.+ m₂ ≡ 0 × m₁ ∈ xs × m₂ ∈ ys) ×
    (∀ n → (∃₂ λ m₁ m₂ → m₁ ℕ.+ m₂ ≡ n × m₁ ∈ xs × m₂ ∈ ys) →
     n ≡ 0)                                                     →⟨ Σ.map (λ { (0 , .0 , refl , 0∈xs , 0∈ys) → 0∈xs , 0∈ys }) idᶠ ⟩

    (0 ∈ xs × 0 ∈ ys) ×
    (∀ n → (∃₂ λ m₁ m₂ → m₁ ℕ.+ m₂ ≡ n × m₁ ∈ xs × m₂ ∈ ys) →
     n ≡ 0)                                                     □

-- The number n is in xs + ys if and only if there are numbers m₁ and
-- m₂ such that m₁ ℕ.+ m₂ is n, m₁ is in xs, and m₂ is in ys.

∈+⇔ :
  ∀ xs ys →
  n ∈ xs + ys ⇔ ∃₂ λ m₁ m₂ → m₁ ℕ.+ m₂ ≡ n × m₁ ∈ xs × m₂ ∈ ys
∈+⇔ xs ys = Addition.∈+⇔ xs ys

------------------------------------------------------------------------
-- Multiplication

-- Some lemmas used to implement multiplication.

private module Multiplication (xs ys : Set-ℕ) where

  -- The membership predicate used for multiplication.

  ∈·? : Nat → Bool
  ∈·? = λ where
    0        → member? xs 0 ∨ member? ys 0
    n@(1+ _) →
      ℕ.∃≤ n λ m₁ → ℕ.∃≤ n λ m₂ →
        (m₁ ℕ.* m₂ ℕ.== n) ∧ member? xs m₁ ∧ member? ys m₂

  -- The correctness property for multiplication.

  ∈·⇔ : T (∈·? n) ⇔ ∃₂ λ m₁ m₂ → m₁ ℕ.* m₂ ≡ n × m₁ ∈ xs × m₂ ∈ ys
  ∈·⇔ {n = n@(1+ _)} =
    T (∈·? n)                                         ⇔⟨ Addition.bin-op-lemma xs ys ⟩

    (∃ λ m₁ → m₁ ℕ.≤ n × ∃ λ m₂ → m₂ ℕ.≤ n ×
     m₁ ℕ.* m₂ ≡ n × m₁ ∈ xs × m₂ ∈ ys)               ⇔⟨ (λ (m₁ , _ , m₂ , _ , m₁m₂≡n , m₁∈xs , m₂∈ys) →
                                                            m₁ , m₂ , m₁m₂≡n , m₁∈xs , m₂∈ys)
                                                       , (λ (m₁ , m₂ , m₁m₂≡n , m₁∈xs , m₂∈ys) →
                                                              m₁
                                                            , (begin
                                                                 m₁         ≤⟨ ℕ.m≤m*n m₁ m₂ ⦃ ℕ.>-nonZero (ℕ.*≡1+→0< {m = m₁} m₁m₂≡n .proj₂) ⦄ ⟩
                                                                 m₁ ℕ.* m₂  ≡⟨ m₁m₂≡n ⟩
                                                                 n          ∎)
                                                            , m₂
                                                            , (begin
                                                                 m₂         ≤⟨ ℕ.m≤n*m m₂ m₁ ⦃ ℕ.>-nonZero (ℕ.*≡1+→0< {m = m₁} m₁m₂≡n .proj₁) ⦄ ⟩
                                                                 m₁ ℕ.* m₂  ≡⟨ m₁m₂≡n ⟩
                                                                 n          ∎)
                                                            , m₁m₂≡n
                                                            , m₁∈xs
                                                            , m₂∈ys)
                                                       ⟩

    (∃₂ λ m₁ m₂ → m₁ ℕ.* m₂ ≡ n × m₁ ∈ xs × m₂ ∈ ys)  □⇔
    where
    open ℕ.≤-Reasoning
  ∈·⇔ {n = 0} =
    T (∈·? 0)                                         ⇔⟨ 0-lemma₁ , uncurry (λ _ → 0-lemma₂) ⟩
    (∃ λ n → 0 ∈ xs × n ∈ ys ⊎ n ∈ xs × 0 ∈ ys)       ⇔⟨ (λ where
                                                            (_ , inj₁ (∈xs , ∈ys)) →
                                                              _ , _ , refl , ∈xs , ∈ys
                                                            (n , inj₂ (∈xs , ∈ys)) →
                                                              _ , _ , ℕ.*-zeroʳ n , ∈xs , ∈ys)
                                                       , (λ where
                                                            (0 , _ , _ , ∈xs , ∈ys) →
                                                              _ , inj₁ (∈xs , ∈ys)
                                                            (1+ _ , 0 , _ , ∈xs , ∈ys) →
                                                              _ , inj₂ (∈xs , ∈ys))
                                                       ⟩
    (∃₂ λ m₁ m₂ → m₁ ℕ.* m₂ ≡ 0 × m₁ ∈ xs × m₂ ∈ ys)  □⇔
    where
    0-lemma₁ : T (∈·? 0) → ∃ λ n → 0 ∈ xs × n ∈ ys ⊎ n ∈ xs × 0 ∈ ys
    0-lemma₁ _  with xs .proj₂ .proj₁
    0-lemma₁ _  | _               with ys .proj₂ .proj₁
    0-lemma₁ _  | 0    , ∈xs , _  | _    , ∈ys , _  =
      _ , inj₁ (∈xs , ∈ys)
    0-lemma₁ _  | 1+ _ , ∈xs , _  | 0    , ∈ys , _  =
      _ , inj₂ (∈xs , ∈ys)
    0-lemma₁ p₁ | 1+ _ , _   , p₂ | 1+ _ , _   , p₃ =
                                                   $⟨ T-∨ .proj₁ p₁ ⟩
      0 ∈ xs ⊎ 0 ∈ ys                              →⟨ (λ { (inj₁ ∈xs) → p₂ _ ℕ.0<1+n ∈xs
                                                         ; (inj₂ ∈ys) → p₃ _ ℕ.0<1+n ∈ys
                                                         }) ⟩
      ⊥                                            →⟨ ⊥-elim ⟩
      (∃ λ n → 0 ∈ xs × n ∈ ys ⊎ n ∈ xs × 0 ∈ ys)  □

    0-lemma₂ : 0 ∈ xs × n ∈ ys ⊎ n ∈ xs × 0 ∈ ys → T (∈·? 0)
    0-lemma₂ (inj₁ (0∈xs , _)) = T-∨ .proj₂ (inj₁ 0∈xs)
    0-lemma₂ (inj₂ (_ , 0∈ys)) = T-∨ .proj₂ (inj₂ 0∈ys)

-- Multiplication.

infixr 45 _·_

_·_ : Set-ℕ → Set-ℕ → Set-ℕ
xs · ys = set
  ∈·?
  (                                                    $⟨ _ , _ , _ , refl , non-empty xs .proj₂ , non-empty ys .proj₂ ⟩
   (∃₃ λ n m₁ m₂ → m₁ ℕ.* m₂ ≡ n × m₁ ∈ xs × m₂ ∈ ys)  ⇔˘⟨ (Σ-cong-⇔ λ _ → ∈·⇔) ⟩→
   (∃ λ n → T (∈·? n))                                 □)
  (case contains-only-0? xs of λ where
     (yes xs-is-𝟘) → inj₁ λ n →
       T (∈·? n)                                         ⇔⟨ ∈·⇔ ⟩→
       (∃₂ λ m₁ m₂ → m₁ ℕ.* m₂ ≡ n × m₁ ∈ xs × m₂ ∈ ys)  →⟨ (λ (_ , _ , m₁m₂≡n , m₁∈xs , _) →
                                                               (_ , _ , m₁m₂≡n , xs-is-𝟘 _ m₁∈xs)) ⟩
       (∃₂ λ m₁ m₂ → m₁ ℕ.* m₂ ≡ n × m₁ ≡ 0)             →⟨ (λ { (_ , _ , refl , refl) → refl }) ⟩
       n ≡ 0                                             □
     (no xs-is-not-𝟘) → case contains-only-0? ys of λ where
       (yes ys-is-𝟘) → inj₁ λ n →
         T (∈·? n)                                         ⇔⟨ ∈·⇔ ⟩→
         (∃₂ λ m₁ m₂ → m₁ ℕ.* m₂ ≡ n × m₁ ∈ xs × m₂ ∈ ys)  →⟨ (λ (m₁ , _ , m₁m₂≡n , _ , m₂∈xs) →
                                                                 (m₁ , _ , m₁m₂≡n , ys-is-𝟘 _ m₂∈xs)) ⟩
         (∃₂ λ m₁ m₂ → m₁ ℕ.* m₂ ≡ n × m₂ ≡ 0)             →⟨ (λ { (m₁ , _ , refl , refl) → ℕ.*-zeroʳ m₁ }) ⟩
         n ≡ 0                                             □
       (no ys-is-not-𝟘) → inj₂
         ((∀ n → T (∈·? n) ⇔ n ≡ 0)                                  →⟨ proj₁ ∘→_ ⟩

          (∀ n → T (∈·? n) → n ≡ 0)                                  ⇔⟨ (Π-cong-⇔ λ _ → ∈·⇔ →-cong-⇔ id⇔) ⟩→

          (∀ n → (∃₂ λ m₁ m₂ → m₁ ℕ.* m₂ ≡ n × m₁ ∈ xs × m₂ ∈ ys) →
           n ≡ 0)                                                    →⟨ Set-[].multiplication-lemma
                                                                          {xs = xs} {ys = ys}
                                                                          (xs-is-not-𝟘 ∘→ proj₂)
                                                                          (ys-is-not-𝟘 ∘→ proj₂) ⟩
          ⊥                                                          □))
  where
  open Multiplication xs ys

-- The number n is in xs · ys if and only if there are numbers m₁ and
-- m₂ such that m₁ ℕ.* m₂ is equal to n, m₁ is in xs, and m₂ is in ys.

∈·⇔ : n ∈ xs · ys ⇔ ∃₂ λ m₁ m₂ → m₁ ℕ.* m₂ ≡ n × m₁ ∈ xs × m₂ ∈ ys
∈·⇔ = Multiplication.∈·⇔ _ _

------------------------------------------------------------------------
-- An instance of Is-non-empty-set for Set-ℕ

-- There is an instance of Is-non-empty-set for Set-ℕ.

is-non-empty-set : Is-non-empty-set Set-ℕ
is-non-empty-set = λ where
  .Is-non-empty-set.is-non-empty-set-[]     → is-non-empty-set-[]
  .Is-non-empty-set._∪_                     → _∪_
  .Is-non-empty-set.∈∪⇔ {xs = xs} {ys = ys} → ∈∪⇔ xs ys
  .Is-non-empty-set._+_                     → _+_
  .Is-non-empty-set.∈+⇔ {xs = xs} {ys = ys} → ∈+⇔ xs ys
  .Is-non-empty-set._·_                     → _·_
  .Is-non-empty-set.∈·⇔                     → ∈·⇔

open Is-non-empty-set is-non-empty-set public
  hiding
    (_∈_; →≡; non-empty; [_]; ∈[]⇔;
     is-non-empty-set-[]; _∪_; ∈∪⇔; _+_; ∈+⇔; _·_; ∈·⇔;
     module Is-𝟘?; module ℕ)

module _ (fe : Function-extensionality lzero lzero) where

  open Is-non-empty-set.Is-𝟘? is-non-empty-set fe is-𝟘?
    public
  open Is-non-empty-set.ℕ     is-non-empty-set fe ℕ (λ {n = n} → ∈ℕ n)
    public
