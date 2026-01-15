------------------------------------------------------------------------
-- An implementation of the set interface in
-- Graded.Modality.Instances.Set.Interval
------------------------------------------------------------------------

module Graded.Modality.Instances.Set.Interval.Implementation where

open import Tools.Bool
open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Nat as N using (Nat; 1+)
open import Tools.Product
open import Tools.PropositionalEquality
import Tools.Reasoning.PartialOrder
open import Tools.Relation
open import Tools.Sum using (_⊎_; inj₁; inj₂)
open import Tools.Unit

import Graded.Modality.Properties.Addition
import Graded.Modality.Properties.Meet
import Graded.Modality.Properties.Multiplication
import Graded.Modality.Properties.PartialOrder
open import Graded.Modality.Instances.Nat-plus-infinity true as ℕ⊎∞
  using (ℕ⊎∞; ⌞_⌟; ∞)
open import Graded.Modality.Instances.Set.Non-empty
  using (Is-non-empty-set-[])
open import Graded.Modality.Instances.Set.Interval
  using (Closure; Is-non-empty-interval)

private
  module NA =
    Graded.Modality.Properties.Addition ℕ⊎∞.ℕ⊎∞-modality
  module NM =
    Graded.Modality.Properties.Meet ℕ⊎∞.ℕ⊎∞-modality
  module NMu =
    Graded.Modality.Properties.Multiplication ℕ⊎∞.ℕ⊎∞-modality
  module NP =
    Graded.Modality.Properties.PartialOrder ℕ⊎∞.ℕ⊎∞-modality

private variable
  A       : Set
  l m     : A
  n n₁ n₂ : Nat

------------------------------------------------------------------------
-- The type

-- Non-empty natural number intervals.

Interval : Set
Interval = ∃₂ λ (m : ℕ⊎∞) (n : Nat) → m ℕ⊎∞.≤ ⌞ n ⌟

private variable
  xs ys : Interval

------------------------------------------------------------------------
-- Equality

-- Equality is decidable.

_≟_ : (xs ys : Interval) → Dec (xs ≡ ys)
(m₁ , n₁ , _) ≟ (m₂ , n₂ , _) =
  case m₁ ℕ⊎∞.≟ m₂ of λ where
    (no m₁≢m₂) → no (m₁≢m₂ ∘→ cong proj₁)
    (yes refl) → case n₁ N.≟ n₂ of λ where
      (no n₁≢n₂) → no (n₁≢n₂ ∘→ cong (proj₁ ∘→ proj₂))
      (yes refl) → yes (cong (λ m≤n → _ , _ , m≤n) ℕ⊎∞.ℕ⊎∞-set)

------------------------------------------------------------------------
-- The relation _∈_

-- The membership relation

infix 10 _∈_

_∈_ : Nat → Interval → Set
n ∈ (l , m , _) = l ℕ⊎∞.≤ ⌞ n ⌟ × ⌞ n ⌟ ℕ⊎∞.≤ ⌞ m ⌟

-- The sets are intervals.

interval : ∀ xs → Closure (_∈ xs) n → n ∈ xs
interval {n = n}
  (l , m , _) (l′ , m′ , l′≤n , n≤m′ , (_ , l′≤m) , (l≤m′ , _)) =
    (begin
       l       ≤⟨ l≤m′ ⟩
       ⌞ m′ ⌟  ≤⟨ ℕ⊎∞.⌞⌟-antitone _ n≤m′ ⟩
       ⌞ n ⌟   ∎)
  , (begin
       ⌞ n ⌟   ≤⟨ ℕ⊎∞.⌞⌟-antitone _ l′≤n ⟩
       ⌞ l′ ⌟  ≤⟨ l′≤m ⟩
       ⌞ m ⌟   ∎)
  where
  open Tools.Reasoning.PartialOrder NP.≤-poset

-- Two sets are equal if their membership relations are pointwise
-- logically equivalent.

→≡ : (∀ n → n ∈ xs ⇔ n ∈ ys) → xs ≡ ys
→≡ {xs = xs} {ys = ys} hyp =
  case lemma₁ xs ys hyp of λ {
    refl →
  case lemma₂ xs ys hyp of λ {
    refl →
  cong (λ m≤n → _ , _ , m≤n) ℕ⊎∞.ℕ⊎∞-set }}
  where
  lemma₁ :
    (xs@(m₁ , n₁ , m₁≤n₁) ys@(m₂ , n₂ , m₂≤n₂) : Interval)  →
    (∀ n → n ∈ xs ⇔ n ∈ ys) →
    m₁ ≡ m₂
  lemma₁ (∞ , _ , _) (∞ , _ , _) =
    λ _ → refl
  lemma₁ xs@(∞ , n₁ , _) ys@(⌞ m₂ ⌟ , n₂ , m₂≤n₂) =
    (∀ n → n ∈ xs ⇔ n ∈ ys)                      →⟨ proj₁ ∘→ (_$ _) ⟩
    ((1+ m₂ N.⊔ n₁) ∈ xs → (1+ m₂ N.⊔ n₁) ∈ ys)  →⟨ _$ (ℕ⊎∞.∞≤ ⌞ 1+ m₂ ⌟ , ℕ⊎∞.⌞⌟-antitone _ (N.m≤n⊔m _ n₁)) ⟩
    (1+ m₂ N.⊔ n₁) ∈ ys                          →⟨ ℕ⊎∞.⌞⌟-antitone⁻¹ ∘→ proj₁ ⟩
    1+ m₂ N.⊔ n₁ N.≤ m₂                          →⟨ N.≤-trans (N.m≤m⊔n _ n₁) ⟩
    m₂ N.< m₂                                    →⟨ N.n≮n _ ⟩
    ⊥                                            →⟨ ⊥-elim ⟩
    ∞ ≡ ⌞ m₂ ⌟                                   □
  lemma₁ xs@(⌞ m₁ ⌟ , n₁ , _) ys@(∞ , n₂ , m₂≤n₂) =
    (∀ n → n ∈ xs ⇔ n ∈ ys)                      →⟨ proj₂ ∘→ (_$ _) ⟩
    ((1+ m₁ N.⊔ n₂) ∈ ys → (1+ m₁ N.⊔ n₂) ∈ xs)  →⟨ _$ (ℕ⊎∞.∞≤ ⌞ 1+ m₁ ⌟ , ℕ⊎∞.⌞⌟-antitone _ (N.m≤n⊔m _ n₂)) ⟩
    (1+ m₁ N.⊔ n₂) ∈ xs                          →⟨ ℕ⊎∞.⌞⌟-antitone⁻¹ ∘→ proj₁ ⟩
    1+ m₁ N.⊔ n₂ N.≤ m₁                          →⟨ N.≤-trans (N.m≤m⊔n _ n₂) ⟩
    m₁ N.< m₁                                    →⟨ N.n≮n _ ⟩
    ⊥                                            →⟨ ⊥-elim ⟩
    ⌞ m₁ ⌟ ≡ ∞                                   □
  lemma₁ (⌞ m₁ ⌟ , _ , m₁≤n₁) (⌞ m₂ ⌟ , _ , m₂≤n₂) = λ hyp →
    NP.≤-antisym
      (begin
         ⌞ m₁ ⌟  ≤⟨ hyp m₂ .proj₂ (NP.≤-refl , m₂≤n₂) .proj₁ ⟩
         ⌞ m₂ ⌟  ∎)
      (begin
         ⌞ m₂ ⌟  ≤⟨ hyp m₁ .proj₁ (NP.≤-refl , m₁≤n₁) .proj₁ ⟩
         ⌞ m₁ ⌟  ∎)
    where
    open Tools.Reasoning.PartialOrder NP.≤-poset

  lemma₂ :
    (xs@(m₁ , n₁ , m₁≤n₁) ys@(m₂ , n₂ , m₂≤n₂) : Interval)  →
    (∀ n → n ∈ xs ⇔ n ∈ ys) →
    n₁ ≡ n₂
  lemma₂ xs@(m₁ , n₁ , m₁≤n₁) ys@(m₂ , n₂ , m₂≤n₂) hyp = N.≤-antisym
    (                     $⟨ hyp _ .proj₂ ⟩
     (n₂ ∈ ys → n₂ ∈ xs)  →⟨ _$ (m₂≤n₂ , NP.≤-refl) ⟩
     n₂ ∈ xs              →⟨ proj₂ ⟩
     ⌞ n₂ ⌟ ℕ⊎∞.≤ ⌞ n₁ ⌟  →⟨ ℕ⊎∞.⌞⌟-antitone⁻¹ ⟩
     n₁ N.≤ n₂            □)
    (                     $⟨ hyp _ .proj₁ ⟩
     (n₁ ∈ xs → n₁ ∈ ys)  →⟨ _$ (m₁≤n₁ , NP.≤-refl) ⟩
     n₁ ∈ ys              →⟨ proj₂ ⟩
     ⌞ n₁ ⌟ ℕ⊎∞.≤ ⌞ n₂ ⌟  →⟨ ℕ⊎∞.⌞⌟-antitone⁻¹ ⟩
     n₂ N.≤ n₁            □)
    where
    open N.≤-Reasoning

-- Every set is non-empty.

non-empty : ∀ xs → ∃ λ n → n ∈ xs
non-empty (_ , n , m≤n) = n , m≤n , NP.≤-refl

------------------------------------------------------------------------
-- Singleton sets

-- A set that contains exactly the given number.

[_] : Nat → Interval
[ n ] = ⌞ n ⌟ , n , NP.≤-refl

-- [_] is correctly defined.

∈[]⇔ : m ∈ [ n ] ⇔ m ≡ n
∈[]⇔ {m = m} {n = n} =
  m ∈ [ n ]                              ⇔⟨ id⇔ ⟩
  ⌞ n ⌟ ℕ⊎∞.≤ ⌞ m ⌟ × ⌞ m ⌟ ℕ⊎∞.≤ ⌞ n ⌟  ⇔⟨ ℕ⊎∞.⌞⌟-injective ∘→ sym ∘→ uncurry NP.≤-antisym
                                          , (λ { refl → NP.≤-refl , NP.≤-refl })
                                          ⟩
  m ≡ n                                  □⇔

------------------------------------------------------------------------
-- The set ℕ

-- A set containing all numbers.

ℕ : Interval
ℕ = ∞ , 0 , ℕ⊎∞.∞≤ ⌞ 0 ⌟

-- ℕ is correctly defined.

∈ℕ : n ∈ ℕ
∈ℕ {n = n} = ℕ⊎∞.∞≤ ⌞ n ⌟ , ℕ⊎∞.≤0 _

------------------------------------------------------------------------
-- Union

-- Union.

infixr 35 _∪_

_∪_ : Interval → Interval → Interval
(m₁ , n₁ , m₁≤n₁) ∪ (m₂ , n₂ , m₂≤n₂) =
    m₁ ℕ⊎∞.∧ m₂
  , n₁ N.⊓ n₂
  , (begin
       m₁ ℕ⊎∞.∧ m₂          ≤⟨ NM.∧-monotone m₁≤n₁ m₂≤n₂ ⟩
       ⌞ n₁ ⌟ ℕ⊎∞.∧ ⌞ n₂ ⌟  ≡⟨⟩
       ⌞ n₁ N.⊔ n₂ ⌟        ≤⟨ ℕ⊎∞.⌞⌟-antitone _ (N.m⊓n≤m⊔n n₁ _) ⟩
       ⌞ n₁ N.⊓ n₂ ⌟        ∎)
  where
  open Tools.Reasoning.PartialOrder NP.≤-poset

-- Union is correctly defined.

∈∪⇔ : ∀ xs ys → n ∈ xs ∪ ys ⇔ Closure (λ n → n ∈ xs ⊎ n ∈ ys) n
∈∪⇔ {n = n} xs@(m₁ , n₁ , m₁≤n₁) ys@(m₂ , n₂ , m₂≤n₂) =
  n ∈ xs ∪ ys                                                ⇔⟨ id⇔ ⟩

  m₁ ℕ⊎∞.∧ m₂ ℕ⊎∞.≤ ⌞ n ⌟ × ⌞ n ⌟ ℕ⊎∞.≤ ⌞ n₁ N.⊓ n₂ ⌟        ⇔⟨ (Σ-cong-⇔ λ _ → ℕ⊎∞.⌞⌟-antitone⁻¹ , ℕ⊎∞.⌞⌟-antitone _) ⟩

  m₁ ℕ⊎∞.∧ m₂ ℕ⊎∞.≤ ⌞ n ⌟ × n₁ N.⊓ n₂ N.≤ n                  ⇔⟨ NM.∧≤⇔ (ℕ⊎∞.≤-total _) ×-cong-⇔ N.⊓≤⇔≤⊎≤ ⟩

  (m₁ ℕ⊎∞.≤ ⌞ n ⌟ ⊎ m₂ ℕ⊎∞.≤ ⌞ n ⌟) × (n₁ N.≤ n ⊎ n₂ N.≤ n)  ⇔⟨ (let case₁ = λ m₁≤n n₁≤n →
                                                                         n₁ , n , n₁≤n , N.≤-refl
                                                                       , inj₁ (NP.≤-trans m₁≤n (ℕ⊎∞.⌞⌟-antitone _ n₁≤n) , NP.≤-refl)
                                                                       , inj₁ (m₁≤n , ℕ⊎∞.⌞⌟-antitone _ n₁≤n)
                                                                     case₂ = λ m₂≤n n₂≤n →
                                                                         n₂ , n , n₂≤n , N.≤-refl
                                                                       , inj₂ (NP.≤-trans m₂≤n (ℕ⊎∞.⌞⌟-antitone _ n₂≤n) , NP.≤-refl)
                                                                       , inj₂ (m₂≤n , ℕ⊎∞.⌞⌟-antitone _ n₂≤n)
                                                                 in λ where
                                                                   (inj₁ m₁≤n , inj₁ n₁≤n) → case₁ m₁≤n n₁≤n
                                                                   (inj₁ m₁≤n , inj₂ n₂≤n) →
                                                                     case N.≤-total n₁ n of λ where
                                                                       (inj₁ n₁≤n) → case₁ m₁≤n n₁≤n
                                                                       (inj₂ n≤n₁) →
                                                                           n₂ , n₁ , n₂≤n , n≤n₁
                                                                         , inj₂ (m₂≤n₂ , NP.≤-refl)
                                                                         , inj₁ (m₁≤n₁ , NP.≤-refl)
                                                                   (inj₂ m₂≤n , inj₁ n₁≤n) →
                                                                     case N.≤-total n₂ n of λ where
                                                                       (inj₁ n₂≤n) → case₂ m₂≤n n₂≤n
                                                                       (inj₂ n≤n₂) →
                                                                           n₁ , n₂ , n₁≤n , n≤n₂
                                                                         , inj₁ (m₁≤n₁ , NP.≤-refl)
                                                                         , inj₂ (m₂≤n₂ , NP.≤-refl)
                                                                   (inj₂ m₂≤n , inj₂ n₂≤n) → case₂ m₂≤n n₂≤n)
                                                              , (λ (_ , _ , l≤n , n≤m , p , q) →
                                                                     (case q of λ where
                                                                        (inj₁ (m₁≤m , _)) →
                                                                          inj₁ (NP.≤-trans m₁≤m (ℕ⊎∞.⌞⌟-antitone _ n≤m))
                                                                        (inj₂ (m₂≤m , _)) →
                                                                          inj₂ (NP.≤-trans m₂≤m (ℕ⊎∞.⌞⌟-antitone _ n≤m)))
                                                                   , (case p of λ where
                                                                        (inj₁ (_ , l≤n₁)) →
                                                                          inj₁ (N.≤-trans (ℕ⊎∞.⌞⌟-antitone⁻¹ l≤n₁) l≤n)
                                                                        (inj₂ (_ , l≤n₂)) →
                                                                          inj₂ (N.≤-trans (ℕ⊎∞.⌞⌟-antitone⁻¹ l≤n₂) l≤n)))
                                                              ⟩
  (∃₂ λ l m → l N.≤ n × n N.≤ m ×
   (m₁ ℕ⊎∞.≤ ⌞ l ⌟ × ⌞ l ⌟ ℕ⊎∞.≤ ⌞ n₁ ⌟ ⊎
    m₂ ℕ⊎∞.≤ ⌞ l ⌟ × ⌞ l ⌟ ℕ⊎∞.≤ ⌞ n₂ ⌟) ×
   (m₁ ℕ⊎∞.≤ ⌞ m ⌟ × ⌞ m ⌟ ℕ⊎∞.≤ ⌞ n₁ ⌟ ⊎
    m₂ ℕ⊎∞.≤ ⌞ m ⌟ × ⌞ m ⌟ ℕ⊎∞.≤ ⌞ n₂ ⌟))                    ⇔⟨ id⇔ ⟩

  Closure (λ n → n ∈ xs ⊎ n ∈ ys) n                          □⇔

------------------------------------------------------------------------
-- The function if-∞

private

  -- The function if-∞ returns its first argument (as a natural
  -- number) if the first argument is not ∞, and otherwise the second
  -- argument.

  if-∞ : ℕ⊎∞ → Nat → Nat
  if-∞ ∞     n = n
  if-∞ ⌞ m ⌟ _ = m

  -- Some lemmas related to if-∞, used in the proofs of ∈+⇔ and ∈·⇔.

  ≤⌞if-∞⌟ : m ℕ⊎∞.≤ ⌞ if-∞ m n ⌟
  ≤⌞if-∞⌟ {m = ∞}     = refl
  ≤⌞if-∞⌟ {m = ⌞ _ ⌟} = NP.≤-refl

  ⌞if-∞⌟≤ : l ℕ⊎∞.≤ ⌞ m ⌟ → m N.≤ n → ⌞ if-∞ l n ⌟ ℕ⊎∞.≤ ⌞ m ⌟
  ⌞if-∞⌟≤ {l = ∞}     _   m≤n = ℕ⊎∞.⌞⌟-antitone _ m≤n
  ⌞if-∞⌟≤ {l = ⌞ l ⌟} l≤m _   = l≤m

  ≤if-∞+if-∞ : l ℕ⊎∞.+ m ℕ⊎∞.≤ ⌞ n ⌟ → n N.≤ if-∞ l n N.+ if-∞ m n
  ≤if-∞+if-∞ {l = ∞} {m = m} {n = n} _ = begin
    n               ≤⟨ N.m≤m+n _ _ ⟩
    n N.+ if-∞ m n  ∎
    where
    open N.≤-Reasoning
  ≤if-∞+if-∞ {l = ⌞ l ⌟} {m = ∞} {n = n} _ = begin
    n        ≤⟨ N.m≤n+m _ _ ⟩
    l N.+ n  ∎
    where
    open N.≤-Reasoning
  ≤if-∞+if-∞ {l = ⌞ l ⌟} {m = ⌞ m ⌟} {n = n} l+m≤n = begin
    n        ≤⟨ ℕ⊎∞.⌞⌟-antitone⁻¹ l+m≤n ⟩
    l N.+ m  ∎
    where
    open N.≤-Reasoning

  ≤if-∞·if-∞ :
    l ℕ⊎∞.· m ℕ⊎∞.≤ ⌞ n ⌟ →
    n N.≤ if-∞ l (n N.⊔ n₁) N.* if-∞ m (n N.⊔ n₂)
  ≤if-∞·if-∞ {l = l} {m = m} {n = 0} {n₁ = n₁} {n₂ = n₂} _ = begin
    0                        ≤⟨ N.z≤n ⟩
    if-∞ l n₁ N.* if-∞ m n₂  ∎
    where
    open N.≤-Reasoning
  ≤if-∞·if-∞ {l = ∞} {m = ∞} {n = n@(1+ _)} {n₁ = n₁} {n₂ = n₂} _ = begin
    n                          ≤⟨ N.m≤m*n n n ⟩
    n N.* n                    ≤⟨ N.*-mono-≤ (N.m≤m⊔n _ n₁) (N.m≤m⊔n _ n₂) ⟩
    (n N.⊔ n₁) N.* (n N.⊔ n₂)  ∎
    where
    open N.≤-Reasoning
  ≤if-∞·if-∞ {l = ∞} {m = ⌞ 0 ⌟} {n = n} {n₁ = n₁} 0≤n = begin
    n                 ≤⟨ ℕ⊎∞.⌞⌟-antitone⁻¹ 0≤n ⟩
    0                 ≡˘⟨ N.*-zeroʳ n ⟩
    n N.* 0           ≤⟨ N.*-mono-≤ (N.m≤m⊔n n _) N.≤-refl ⟩
    (n N.⊔ n₁) N.* 0  ∎
    where
    open N.≤-Reasoning
  ≤if-∞·if-∞ {l = ∞} {m = ⌞ m@(1+ _) ⌟} {n = n} {n₁ = n₁} _ = begin
    n                 ≤⟨ N.m≤m*n n m ⟩
    n N.* m           ≤⟨ N.*-mono-≤ (N.m≤m⊔n n _) N.≤-refl ⟩
    (n N.⊔ n₁) N.* m  ∎
    where
    open N.≤-Reasoning
  ≤if-∞·if-∞ {l = ⌞ 0 ⌟} {m = ∞} {n = n} 0≤n = begin
    n  ≤⟨ ℕ⊎∞.⌞⌟-antitone⁻¹ 0≤n ⟩
    0  ∎
    where
    open N.≤-Reasoning
  ≤if-∞·if-∞ {l = ⌞ l@(1+ _) ⌟} {m = ∞} {n = n} {n₂ = n₂} _ = begin
    n                 ≤⟨ N.m≤n*m n l ⟩
    l N.* n           ≤⟨ N.*-mono-≤ (N.≤-refl {x = l}) (N.m≤m⊔n _ _) ⟩
    l N.* (n N.⊔ n₂)  ∎
    where
    open N.≤-Reasoning
  ≤if-∞·if-∞ {l = ⌞ l ⌟} {m = ⌞ m ⌟} {n = n} {n₁ = n₁} {n₂ = n₂} lm≤n = begin
    n        ≤⟨ ℕ⊎∞.⌞⌟-antitone⁻¹ (subst (ℕ⊎∞._≤ _) ℕ⊎∞.⌞⌟·⌞⌟≡⌞*⌟ lm≤n) ⟩
    l N.* m  ∎
    where
    open N.≤-Reasoning

------------------------------------------------------------------------
-- Addition

-- Addition.

infixr 40 _+_

_+_ : Interval → Interval → Interval
(m₁ , n₁ , m₁≤n₁) + (m₂ , n₂ , m₂≤n₂) =
    m₁ ℕ⊎∞.+ m₂
  , n₁ N.+ n₂
  , (begin
       m₁ ℕ⊎∞.+ m₂          ≤⟨ NA.+-monotone m₁≤n₁ m₂≤n₂ ⟩
       ⌞ n₁ ⌟ ℕ⊎∞.+ ⌞ n₂ ⌟  ≡⟨⟩
       ⌞ n₁ N.+ n₂ ⌟        ∎)
  where
  open Tools.Reasoning.PartialOrder NP.≤-poset

-- Addition is correctly implemented.

∈+⇔ :
  ∀ xs ys →
  n ∈ xs + ys ⇔
  Closure (λ n → ∃₂ λ m₁ m₂ → m₁ N.+ m₂ ≡ n × m₁ ∈ xs × m₂ ∈ ys) n
∈+⇔ {n = n} xs@(m₁ , n₁ , m₁≤n₁) ys@(m₂ , n₂ , m₂≤n₂) =
  n ∈ xs + ys                                                       ⇔⟨ id⇔ ⟩

  m₁ ℕ⊎∞.+ m₂ ℕ⊎∞.≤ ⌞ n ⌟ × ⌞ n ⌟ ℕ⊎∞.≤ ⌞ n₁ N.+ n₂ ⌟               ⇔⟨ (Σ-cong-⇔ λ _ → ℕ⊎∞.⌞⌟-antitone⁻¹ , ℕ⊎∞.⌞⌟-antitone _) ⟩

  m₁ ℕ⊎∞.+ m₂ ℕ⊎∞.≤ ⌞ n ⌟ × n₁ N.+ n₂ N.≤ n                         ⇔⟨ (λ (m₁+m₂≤n , n₁+n₂≤n) →
                                                                            n₁ , n₂ , if-∞ m₁ n , if-∞ m₂ n
                                                                          , n₁+n₂≤n
                                                                          , ≤if-∞+if-∞ m₁+m₂≤n
                                                                          , m₁≤n₁
                                                                          , NP.≤-refl
                                                                          , ≤⌞if-∞⌟
                                                                          , ⌞if-∞⌟≤ m₁≤n₁
                                                                              (let open N.≤-Reasoning in begin
                                                                                 n₁         ≤⟨ N.m≤m+n _ _ ⟩
                                                                                 n₁ N.+ n₂  ≤⟨ n₁+n₂≤n ⟩
                                                                                 n          ∎)
                                                                          , m₂≤n₂
                                                                          , NP.≤-refl
                                                                          , ≤⌞if-∞⌟
                                                                          , ⌞if-∞⌟≤ m₂≤n₂
                                                                              (let open N.≤-Reasoning in begin
                                                                                 n₂         ≤⟨ N.m≤n+m _ _ ⟩
                                                                                 n₁ N.+ n₂  ≤⟨ n₁+n₂≤n ⟩
                                                                                 n          ∎))
                                                                     , (λ ( k₁ , k₂ , k₃ , k₄ , k₁+k₂≤n , n≤k₃+k₄
                                                                          , _ , k₁≤n₁ , m₁≤k₃ , _
                                                                          , _ , k₂≤n₂ , m₂≤k₄ , _
                                                                          ) →
                                                                            (let open Tools.Reasoning.PartialOrder NP.≤-poset in begin
                                                                               m₁ ℕ⊎∞.+ m₂          ≤⟨ NA.+-monotone m₁≤k₃ m₂≤k₄ ⟩
                                                                               ⌞ k₃ ⌟ ℕ⊎∞.+ ⌞ k₄ ⌟  ≡⟨⟩
                                                                               ⌞ k₃ N.+ k₄ ⌟        ≤⟨ ℕ⊎∞.⌞⌟-antitone _ n≤k₃+k₄ ⟩
                                                                               ⌞ n ⌟                ∎)
                                                                          , (let open N.≤-Reasoning in begin
                                                                               n₁ N.+ n₂  ≤⟨ N.+-mono-≤
                                                                                               (ℕ⊎∞.⌞⌟-antitone⁻¹ k₁≤n₁)
                                                                                               (ℕ⊎∞.⌞⌟-antitone⁻¹ k₂≤n₂) ⟩
                                                                               k₁ N.+ k₂  ≤⟨ k₁+k₂≤n ⟩
                                                                               n          ∎))
                                                                     ⟩
  (∃₄ λ k₁ k₂ k₃ k₄ →
   k₁ N.+ k₂ N.≤ n × n N.≤ k₃ N.+ k₄ ×
   m₁ ℕ⊎∞.≤ ⌞ k₁ ⌟ × ⌞ k₁ ⌟ ℕ⊎∞.≤ ⌞ n₁ ⌟ ×
   m₁ ℕ⊎∞.≤ ⌞ k₃ ⌟ × ⌞ k₃ ⌟ ℕ⊎∞.≤ ⌞ n₁ ⌟ ×
   m₂ ℕ⊎∞.≤ ⌞ k₂ ⌟ × ⌞ k₂ ⌟ ℕ⊎∞.≤ ⌞ n₂ ⌟ ×
   m₂ ℕ⊎∞.≤ ⌞ k₄ ⌟ × ⌞ k₄ ⌟ ℕ⊎∞.≤ ⌞ n₂ ⌟)                         ⇔⟨ (λ ( _ , _ , _ , _ , ≤n , n≤
                                                                        , m₁≤k₁ , k₁≤n₁ , m₁≤k₃ , k₃≤n₁
                                                                        , m₂≤k₂ , k₂≤n₂ , m₂≤k₄ , k₄≤n₂
                                                                        ) →
                                                                          _ , _ , ≤n , n≤
                                                                        , (_ , _ , refl , (m₁≤k₁ , k₁≤n₁) , (m₂≤k₂ , k₂≤n₂))
                                                                        , (_ , _ , refl , (m₁≤k₃ , k₃≤n₁) , (m₂≤k₄ , k₄≤n₂)))
                                                                   , (λ { ( _ , _ , ≤n , n≤
                                                                          , (_ , _ , refl , (m₁≤k₁ , k₁≤n₁) , (m₂≤k₂ , k₂≤n₂))
                                                                          , (_ , _ , refl , (m₁≤k₃ , k₃≤n₁) , (m₂≤k₄ , k₄≤n₂))
                                                                          ) →
                                                                            _ , _ , _ , _ , ≤n , n≤
                                                                          , m₁≤k₁ , k₁≤n₁ , m₁≤k₃ , k₃≤n₁
                                                                          , m₂≤k₂ , k₂≤n₂ , m₂≤k₄ , k₄≤n₂ })
                                                                   ⟩
  (∃₂ λ l m → l N.≤ n × n N.≤ m ×
   (∃₂ λ k₁ k₂ → k₁ N.+ k₂ ≡ l ×
    (m₁ ℕ⊎∞.≤ ⌞ k₁ ⌟ × ⌞ k₁ ⌟ ℕ⊎∞.≤ ⌞ n₁ ⌟) ×
    (m₂ ℕ⊎∞.≤ ⌞ k₂ ⌟ × ⌞ k₂ ⌟ ℕ⊎∞.≤ ⌞ n₂ ⌟)) ×
   (∃₂ λ k₁ k₂ → k₁ N.+ k₂ ≡ m ×
    (m₁ ℕ⊎∞.≤ ⌞ k₁ ⌟ × ⌞ k₁ ⌟ ℕ⊎∞.≤ ⌞ n₁ ⌟) ×
    (m₂ ℕ⊎∞.≤ ⌞ k₂ ⌟ × ⌞ k₂ ⌟ ℕ⊎∞.≤ ⌞ n₂ ⌟)))                       ⇔⟨ id⇔ ⟩

  Closure (λ n → ∃₂ λ m₁ m₂ → m₁ N.+ m₂ ≡ n × m₁ ∈ xs × m₂ ∈ ys) n  □⇔

------------------------------------------------------------------------
-- Multiplication

-- Multiplication.

infixr 45 _·_

_·_ : Interval → Interval → Interval
(m₁ , n₁ , m₁≤n₁) · (m₂ , n₂ , m₂≤n₂) =
    m₁ ℕ⊎∞.· m₂
  , n₁ N.* n₂
  , (begin
       m₁ ℕ⊎∞.· m₂          ≤⟨ NMu.·-monotone m₁≤n₁ m₂≤n₂ ⟩
       ⌞ n₁ ⌟ ℕ⊎∞.· ⌞ n₂ ⌟  ≡⟨ ℕ⊎∞.⌞⌟·⌞⌟≡⌞*⌟ ⟩
       ⌞ n₁ N.* n₂ ⌟        ∎)
  where
  open Tools.Reasoning.PartialOrder NP.≤-poset

-- Multiplication is correctly implemented.

∈·⇔ :
  ∀ xs ys →
  n ∈ xs · ys ⇔
  Closure (λ n → ∃₂ λ m₁ m₂ → m₁ N.* m₂ ≡ n × m₁ ∈ xs × m₂ ∈ ys) n
∈·⇔ {n = n} xs@(m₁ , n₁ , m₁≤n₁) ys@(m₂ , n₂ , m₂≤n₂) =
  n ∈ xs · ys                                                       ⇔⟨ id⇔ ⟩

  m₁ ℕ⊎∞.· m₂ ℕ⊎∞.≤ ⌞ n ⌟ × ⌞ n ⌟ ℕ⊎∞.≤ ⌞ n₁ N.* n₂ ⌟               ⇔⟨ (Σ-cong-⇔ λ _ → ℕ⊎∞.⌞⌟-antitone⁻¹ , ℕ⊎∞.⌞⌟-antitone _) ⟩

  m₁ ℕ⊎∞.· m₂ ℕ⊎∞.≤ ⌞ n ⌟ × n₁ N.* n₂ N.≤ n                         ⇔⟨ (λ (m₁m₂≤n , n₁n₂≤n) →
                                                                            n₁ , n₂ , if-∞ m₁ (n N.⊔ n₁) , if-∞ m₂ (n N.⊔ n₂)
                                                                          , n₁n₂≤n
                                                                          , ≤if-∞·if-∞ m₁m₂≤n
                                                                          , m₁≤n₁
                                                                          , NP.≤-refl
                                                                          , ≤⌞if-∞⌟
                                                                          , ⌞if-∞⌟≤ m₁≤n₁
                                                                              (let open N.≤-Reasoning in begin
                                                                                 n₁        ≤⟨ N.m≤n⊔m _ _ ⟩
                                                                                 n N.⊔ n₁  ∎)
                                                                          , m₂≤n₂
                                                                          , NP.≤-refl
                                                                          , ≤⌞if-∞⌟
                                                                          , ⌞if-∞⌟≤ m₂≤n₂
                                                                              (let open N.≤-Reasoning in begin
                                                                                 n₂        ≤⟨ N.m≤n⊔m _ _ ⟩
                                                                                 n N.⊔ n₂  ∎))
                                                                     , (λ ( k₁ , k₂ , k₃ , k₄ , k₁k₂≤n , n≤k₃k₄
                                                                          , _ , k₁≤n₁ , m₁≤k₃ , _
                                                                          , _ , k₂≤n₂ , m₂≤k₄ , _
                                                                          ) →
                                                                            (let open Tools.Reasoning.PartialOrder NP.≤-poset in begin
                                                                               m₁ ℕ⊎∞.· m₂          ≤⟨ NMu.·-monotone m₁≤k₃ m₂≤k₄ ⟩
                                                                               ⌞ k₃ ⌟ ℕ⊎∞.· ⌞ k₄ ⌟  ≡⟨ ℕ⊎∞.⌞⌟·⌞⌟≡⌞*⌟ ⟩
                                                                               ⌞ k₃ N.* k₄ ⌟        ≤⟨ ℕ⊎∞.⌞⌟-antitone _ n≤k₃k₄ ⟩
                                                                               ⌞ n ⌟                ∎)
                                                                          , (let open N.≤-Reasoning in begin
                                                                               n₁ N.* n₂  ≤⟨ N.*-mono-≤
                                                                                               (ℕ⊎∞.⌞⌟-antitone⁻¹ k₁≤n₁)
                                                                                               (ℕ⊎∞.⌞⌟-antitone⁻¹ k₂≤n₂) ⟩
                                                                               k₁ N.* k₂  ≤⟨ k₁k₂≤n ⟩
                                                                               n          ∎))
                                                                     ⟩
  (∃₄ λ k₁ k₂ k₃ k₄ →
   k₁ N.* k₂ N.≤ n × n N.≤ k₃ N.* k₄ ×
   m₁ ℕ⊎∞.≤ ⌞ k₁ ⌟ × ⌞ k₁ ⌟ ℕ⊎∞.≤ ⌞ n₁ ⌟ ×
   m₁ ℕ⊎∞.≤ ⌞ k₃ ⌟ × ⌞ k₃ ⌟ ℕ⊎∞.≤ ⌞ n₁ ⌟ ×
   m₂ ℕ⊎∞.≤ ⌞ k₂ ⌟ × ⌞ k₂ ⌟ ℕ⊎∞.≤ ⌞ n₂ ⌟ ×
   m₂ ℕ⊎∞.≤ ⌞ k₄ ⌟ × ⌞ k₄ ⌟ ℕ⊎∞.≤ ⌞ n₂ ⌟)                         ⇔⟨ (λ ( _ , _ , _ , _ , ≤n , n≤
                                                                        , m₁≤k₁ , k₁≤n₁ , m₁≤k₃ , k₃≤n₁
                                                                        , m₂≤k₂ , k₂≤n₂ , m₂≤k₄ , k₄≤n₂
                                                                        ) →
                                                                          _ , _ , ≤n , n≤
                                                                        , (_ , _ , refl , (m₁≤k₁ , k₁≤n₁) , (m₂≤k₂ , k₂≤n₂))
                                                                        , (_ , _ , refl , (m₁≤k₃ , k₃≤n₁) , (m₂≤k₄ , k₄≤n₂)))
                                                                   , (λ { ( _ , _ , ≤n , n≤
                                                                          , (_ , _ , refl , (m₁≤k₁ , k₁≤n₁) , (m₂≤k₂ , k₂≤n₂))
                                                                          , (_ , _ , refl , (m₁≤k₃ , k₃≤n₁) , (m₂≤k₄ , k₄≤n₂))
                                                                          ) →
                                                                            _ , _ , _ , _ , ≤n , n≤
                                                                          , m₁≤k₁ , k₁≤n₁ , m₁≤k₃ , k₃≤n₁
                                                                          , m₂≤k₂ , k₂≤n₂ , m₂≤k₄ , k₄≤n₂ })
                                                                   ⟩
  (∃₂ λ l m → l N.≤ n × n N.≤ m ×
   (∃₂ λ k₁ k₂ → k₁ N.* k₂ ≡ l ×
    (m₁ ℕ⊎∞.≤ ⌞ k₁ ⌟ × ⌞ k₁ ⌟ ℕ⊎∞.≤ ⌞ n₁ ⌟) ×
    (m₂ ℕ⊎∞.≤ ⌞ k₂ ⌟ × ⌞ k₂ ⌟ ℕ⊎∞.≤ ⌞ n₂ ⌟)) ×
   (∃₂ λ k₁ k₂ → k₁ N.* k₂ ≡ m ×
    (m₁ ℕ⊎∞.≤ ⌞ k₁ ⌟ × ⌞ k₁ ⌟ ℕ⊎∞.≤ ⌞ n₁ ⌟) ×
    (m₂ ℕ⊎∞.≤ ⌞ k₂ ⌟ × ⌞ k₂ ⌟ ℕ⊎∞.≤ ⌞ n₂ ⌟)))                       ⇔⟨ id⇔ ⟩

  Closure (λ n → ∃₂ λ m₁ m₂ → m₁ N.* m₂ ≡ n × m₁ ∈ xs × m₂ ∈ ys) n  □⇔

------------------------------------------------------------------------
-- An instance of Is-non-empty-interval for Interval

-- There is an instance of Is-non-empty-interval for Interval.

is-non-empty-interval : Is-non-empty-interval Interval
is-non-empty-interval = λ where
  .Is-non-empty-interval.is-non-empty-set-[] → λ where
    .Is-non-empty-set-[]._∈_                 → _∈_
    .Is-non-empty-set-[].Ext                 → Lift _ ⊤
    .Is-non-empty-set-[].→≡ _                → →≡
    .Is-non-empty-set-[].non-empty {xs = xs} → non-empty xs
    .Is-non-empty-set-[].[_]                 → [_]
    .Is-non-empty-set-[].∈[]⇔                → ∈[]⇔
  .Is-non-empty-interval.interval {xs = xs}      → interval xs
  .Is-non-empty-interval.ℕ                       → ℕ
  .Is-non-empty-interval.∈ℕ                      → ∈ℕ
  .Is-non-empty-interval._∪_                     → _∪_
  .Is-non-empty-interval.∈∪⇔ {xs = xs} {ys = ys} → ∈∪⇔ xs ys
  .Is-non-empty-interval._+_                     → _+_
  .Is-non-empty-interval.∈+⇔ {xs = xs} {ys = ys} → ∈+⇔ xs ys
  .Is-non-empty-interval._·_                     → _·_
  .Is-non-empty-interval.∈·⇔ {xs = xs} {ys = ys} → ∈·⇔ xs ys
  .Is-non-empty-interval.is-𝟘? xs                →
    case xs ≟ [ 0 ] of λ where
      (yes xs≡𝟘) → inj₁ (λ _ → xs≡𝟘)
      (no xs≢𝟘)  → inj₂ xs≢𝟘

open Is-non-empty-interval is-non-empty-interval public
  hiding
    (_∈_; Ext; →≡; non-empty; [_]; ∈[]⇔;
     is-non-empty-set-[]; interval; _∪_; ∈∪⇔; _+_; ∈+⇔; _·_; ∈·⇔; ℕ; ∈ℕ)
