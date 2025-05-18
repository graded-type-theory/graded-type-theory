------------------------------------------------------------------------
-- The natural numbers.
------------------------------------------------------------------------

module Tools.Nat where

-- We reexport Agda's built-in type of natural numbers.

open import Agda.Builtin.Nat using (Nat; _+_; _*_; _==_) public
open import Agda.Builtin.Nat using (zero; suc)
import Data.Fin as F
import Data.Fin.Properties as FP
open import Data.Nat.Base
open Data.Nat.Base public
  using (_≤_; _<_; pred; _⊔_; _⊓_; >-nonZero; nonZero; _∸_)
open _≤_ public
open import Data.Nat.DivMod
open Data.Nat.DivMod using (_/_; m/n*n≤m; m*n/n≡m) public
open import Data.Nat.Properties
open import Data.Nat using (_<′_; ≤′-refl; ≤′-step; _≤′_) public
open Data.Nat.Properties
  using (_≟_; _<?_; ≤-total;
         +-identityʳ; +-assoc; +-comm; +-0-isCommutativeMonoid; +-suc;
         +-cancelˡ-≡;
         *-identityˡ; *-identityʳ; *-assoc; *-comm; *-zeroʳ; *-cancelˡ-≡;
         *-suc; *-1-isCommutativeMonoid; +-*-isSemiring; ⊔-isSemilattice;
         m*n≡0⇒m≡0∨n≡0;
         ⊔-identityʳ; ⊔-assoc; ⊔-comm; ⊔-idem; m≥n⇒m⊔n≡m; m≤n⇒m⊔n≡n; m⊔n≡m⇒n≤m; m⊔n≡n⇒m≤n;
         ⊓-assoc; ⊓-comm;
         +-distribˡ-⊔; +-distribʳ-⊔; ∸-distribʳ-⊔;
         *-distribˡ-+; *-distribʳ-+; *-distribˡ-⊔; *-distribʳ-⊔;
         ⊓-distribʳ-⊔; ⊔-distribʳ-⊓;
         ⊔-absorbs-⊓; ⊓-absorbs-⊔;
         ≤-refl; ≤-reflexive; ≤-trans; ≤-antisym; module ≤-Reasoning;
         ≤-<-trans;
         n≮n; ≤∧≢⇒<; m<n⇒n≢0;
         ≤⇒pred≤;
         +-mono-≤; m≤m+n; m≤n+m; m+n≤o⇒n≤o; 0<1+n; n≤1+n; m≤n⇒m≤1+n;
         *-mono-≤; m≤m*n; m≤n*m; m+1+n≰m;
         m≤m⊔n; m≤n⊔m;
         m<n⊓o⇒m<n; m<n⊓o⇒m<o; ⊓-pres-m<;
         m⊓n≤m⊔n; m+n∸n≡m; m∸n+n≡m; ⊔-mono-<;
         <⇒<′; <′⇒<; ≤′⇒≤; ≤′-trans; z≤′n)
  renaming (suc-injective to 1+-injective;
            s≤′s to 1+≤′1+)
  public
open import Data.Nat.Show using (show) public
open import Relation.Binary using (Tri)
open Tri

open import Tools.Bool
open import Tools.Empty
open import Tools.Function
open import Tools.Level using (Level; lzero)
open import Tools.Product as Σ
open import Tools.PropositionalEquality
open import Tools.Relation
open import Tools.Sum as ⊎ using (_⊎_; inj₁; inj₂)

pattern 1+ n = suc n
pattern 2+ n = 1+ (1+ n)
pattern 3+ n = 1+ (2+ n)
pattern 4+ n = 1+ (3+ n)

private variable
  a             : Level
  k m m′ n n′ o : Nat
  p             : Nat → Bool

-- Nat is a set.

Nat-set : Is-set Nat
Nat-set {x = zero}  {y = zero}  {x = refl} {y = refl} = refl
Nat-set {x = zero}  {y = suc _} {x = ()}
Nat-set {x = suc _} {y = zero}  {x = ()}
Nat-set {x = suc m} {y = suc n} {x = p}    {y = q}    =
                                                   $⟨ Nat-set {x = m} {y = n} ⟩
  cong pred p ≡ cong pred q                        →⟨ cong (cong suc) ⟩
  cong suc (cong pred p) ≡ cong suc (cong pred q)  →⟨ (λ hyp → trans (sym (lemma _)) (trans hyp (lemma _))) ⟩
  p ≡ q                                            □
  where
  lemma : (p : suc m ≡ suc n) → cong suc (cong pred p) ≡ p
  lemma refl = refl

-- The inequality m ⊓ n ≤ o holds if and only if either m ≤ o or n ≤ o
-- holds.

⊓≤⇔≤⊎≤ : m ⊓ n ≤ o ⇔ (m ≤ o ⊎ n ≤ o)
⊓≤⇔≤⊎≤ {m = m} {n = n} {o = o} =
    (λ m⊓n≤o →
       case ≤-total m n of λ where
         (inj₁ m≤n) → inj₁ $ begin
           m      ≤⟨ ⊓-glb ≤-refl m≤n ⟩
           m ⊓ n  ≤⟨ m⊓n≤o ⟩
           o      ∎
         (inj₂ n≤m) → inj₂ $ begin
           n      ≤⟨ ⊓-glb n≤m ≤-refl ⟩
           m ⊓ n  ≤⟨ m⊓n≤o ⟩
           o      ∎)
  , (λ where
       (inj₁ m≤o) → begin
         m ⊓ n  ≤⟨ m⊓n≤m _ _ ⟩
         m      ≤⟨ m≤o ⟩
         o      ∎
       (inj₂ n≤o) → begin
         m ⊓ n  ≤⟨ m⊓n≤n _ _ ⟩
         n      ≤⟨ n≤o ⟩
         o      ∎)
  where
  open ≤-Reasoning

-- The inequality m ≤ n ⊔ o holds if and only if either m ≤ n or m ≤ o
-- holds.

≤⊔⇔≤⊎≤ : m ≤ n ⊔ o ⇔ (m ≤ n ⊎ m ≤ o)
≤⊔⇔≤⊎≤ {m = m} {n = n} {o = o} =
    (λ m≤n⊔o →
       case ≤-total n o of λ where
         (inj₁ n≤o) → inj₂ $ begin
           m      ≤⟨ m≤n⊔o ⟩
           n ⊔ o  ≤⟨ ⊔-lub n≤o ≤-refl ⟩
           o      ∎
         (inj₂ o≤n) → inj₁ $ begin
           m      ≤⟨ m≤n⊔o ⟩
           n ⊔ o  ≤⟨ ⊔-lub ≤-refl o≤n ⟩
           n      ∎)
  , (λ where
       (inj₁ m≤n) → begin
         m      ≤⟨ m≤n ⟩
         n      ≤⟨ m≤m⊔n _ _ ⟩
         n ⊔ o  ∎
       (inj₂ m≤o) → begin
         m      ≤⟨ m≤o ⟩
         o      ≤⟨ m≤n⊔m _ _ ⟩
         n ⊔ o  ∎)
  where
  open ≤-Reasoning

-- If m * n ≡ 1+ o, then 0 < m and 0 < n.

*≡1+→0< : m * n ≡ 1+ o → 0 < m × 0 < n
*≡1+→0< {m = 0}                       = λ ()
*≡1+→0< {m = 1+ _} {n = 1+ _}         = λ _ → s≤s z≤n , s≤s z≤n
*≡1+→0< {m = 1+ m} {n = 0}    {o = o} =
  m * 0 ≡ 1+ o      →⟨ trans (sym (*-zeroʳ m)) ⟩
  0 ≡ 1+ o          →⟨ (λ ()) ⟩
  0 < 1+ m × 0 < 0  □

private

  -- If 1+ m * n ≤ k + 1+ m * o for some k ≤ m, then
  -- 1+ m * n ≤ 1+ m * o.

  1+*≤+1+*→1+*≤1+* :
    k ≤ m →
    1+ m * n ≤ k + 1+ m * o →
    1+ m * n ≤ 1+ m * o
  1+*≤+1+*→1+*≤1+* {m = m} {n = 0} {o = o} _ _ =
                         $⟨ _≤_.z≤n ⟩
    0 ≤ 1+ m * o         ≡⟨ cong (_≤ 1+ m * o) (sym (*-zeroʳ m)) ⟩→
    1+ m * 0 ≤ 1+ m * o  □
  1+*≤+1+*→1+*≤1+* {k = k} {m = m} {n = 1+ n} {o = 0} k≤m =
    1+ m * 1+ n ≤ k + m * 0  ≡⟨ cong₂ _≤_ (*-comm (1+ m) (1+ n)) (cong (k +_) (*-zeroʳ m)) ⟩→
    1+ n * 1+ m ≤ k + 0      ≡⟨ cong (_ ≤_) (+-identityʳ _) ⟩→
    1+ n * 1+ m ≤ k          →⟨ idᶠ ⟩
    1+ m + n * 1+ m ≤ k      →⟨ m+n≤o⇒m≤o _ ⟩
    m < k                    →⟨ flip ≤-trans k≤m ⟩
    m < m                    →⟨ <-irrefl refl ⟩
    ⊥                        →⟨ ⊥-elim ⟩
    1+ m * 1+ n ≤ m * 0      □
  1+*≤+1+*→1+*≤1+* {k = k} {m = m} {n = 1+ n} {o = 1+ o} k≤m =
    1+ m * 1+ n ≤ k + 1+ m * 1+ o            ≡⟨ cong₂ _≤_ (*-suc (1+ m) _) (cong (k +_) (*-suc (1+ m) _)) ⟩→
    1+ m + 1+ m * n ≤ k + (1+ m + 1+ m * o)  ≡⟨ cong (1+ m + 1+ m * n ≤_) $
                                                trans (sym (+-assoc k (1+ m) _)) $
                                                trans (cong (_+ 1+ m * o) (+-comm k _)) $
                                                +-assoc (1+ m) _ _ ⟩→
    1+ m + 1+ m * n ≤ 1+ m + (k + 1+ m * o)  →⟨ +-cancelˡ-≤ (1+ m) (n + m * n) (k + (o + m * o)) ⟩
    1+ m * n ≤ k + 1+ m * o                  →⟨ 1+*≤+1+*→1+*≤1+* k≤m ⟩
    1+ m * n ≤ 1+ m * o                      →⟨ +-mono-≤ (≤-refl {x = 1+ m}) ⟩
    1+ m + 1+ m * n ≤ 1+ m + 1+ m * o        ≡⟨ sym $ cong₂ _≤_ (*-suc (1+ m) _) (*-suc (1+ m) _) ⟩→
    1+ m * 1+ n ≤ 1+ m * 1+ o                □

-- If 1+ m * n ≤ o, then n ≤ o / 1+ m.

*≤→≤/ : 1+ m * n ≤ o → n ≤ o / 1+ m
*≤→≤/ {m = m} {n = n} {o = o} = helper (o divMod 1+ m)
  where
  helper :
    (d : DivMod o (1+ m)) →
    1+ m * n ≤ o → n ≤ d .DivMod.quotient
  helper (record { quotient = q; remainder = r; property = refl }) =
    1+ m * n ≤ F.toℕ r + q * 1+ m  ≡⟨ cong (λ o → 1+ m * n ≤ F.toℕ r + o) (*-comm q _) ⟩→
    1+ m * n ≤ F.toℕ r + 1+ m * q  →⟨ 1+*≤+1+*→1+*≤1+* (FP.toℕ≤pred[n] r) ⟩
    1+ m * n ≤ 1+ m * q            →⟨ *-cancelˡ-≤ (1+ m) ⟩
    n ≤ q                          □

-- T (m == n) is logically equivalent to m ≡ n.

T-== : T (m == n) ⇔ m ≡ n
T-== = ≡ᵇ⇒≡ _ _ , ≡⇒≡ᵇ _ _

-- ∃< n p is true if there is some m < n such that p m holds.

∃< : Nat → (Nat → Bool) → Bool
∃< 0      p = false
∃< (1+ n) p = p n ∨ ∃< n p

-- ∃< is correctly defined.

∃<⇔ : T (∃< n p) ⇔ (∃ λ m → m < n × T (p m))
∃<⇔ {n = 0} {p = p} =
  ⊥                          ⇔⟨ (⊥-elim , λ { (_ , () , _) }) ⟩
  (∃ λ m → m < 0 × T (p m))  □⇔
∃<⇔ {n = 1+ n} {p = p} =
  T (p n ∨ ∃< n p)                     ⇔⟨ T-∨ ⟩
  T (p n) ⊎ T (∃< n p)                 ⇔⟨ id⇔ ⊎-cong-⇔ ∃<⇔ ⟩
  T (p n) ⊎ (∃ λ m → m < n × T (p m))  ⇔⟨ (λ where
                                             (inj₁ p-n)             → n , ≤-refl , p-n
                                             (inj₂ (m , m<n , p-m)) → m , ≤-trans m<n (n≤1+n _) , p-m)
                                        , (λ (m , m<1+n , p-m) →
                                             case <-cmp m n of λ where
                                               (tri< m<n _    _)   → inj₂ (m , m<n , p-m)
                                               (tri≈ _   refl _)   → inj₁ p-m
                                               (tri> _   _    m>n) → ⊥-elim (m+n≮n _ _ (≤-trans m<1+n m>n)))
                                        ⟩
  (∃ λ m → m < 1+ n × T (p m))         □⇔

-- ∃≤ n p is true if there is some m ≤ n such that p m holds.

∃≤ : Nat → (Nat → Bool) → Bool
∃≤ n = ∃< (1+ n)

-- ∃≤ is correctly defined.

∃≤⇔ : T (∃≤ n p) ⇔ (∃ λ m → m ≤ n × T (p m))
∃≤⇔ {n = n} {p = p} =
  T (∃≤ n p)                    ⇔⟨ id⇔ ⟩
  T (∃< (1+ n) p)               ⇔⟨ ∃<⇔ ⟩
  (∃ λ m → m < 1+ n × T (p m))  ⇔⟨ (Σ-cong-⇔ λ _ → ((λ { (s≤s m≤n) → m≤n }) , s≤s) ×-cong-⇔ id⇔) ⟩
  (∃ λ m → m ≤ n × T (p m))     □⇔

-- ∃-least P means that there is a least number n for which P n holds.

∃-least : (ℕ → Set a) → Set a
∃-least P = ∃ λ n → P n × ∀ m → m < n → ¬ P m

-- A decidable predicate holds for some number if and only if there is
-- a least number for which it holds.

∃⇔∃-least : (∃ λ n → T (p n)) ⇔ ∃-least (λ n → T (p n))
∃⇔∃-least = (uncurry λ _ → ∃→∃-least) , Σ.map idᶠ proj₁
  where
  ∃→∃-least : T (p n) → ∃-least (λ n → T (p n))
  ∃→∃-least {n = 0} ok =
    0 , ok , λ _ ()
  ∃→∃-least {p = p} {n = 1+ n} ok = lemma _ refl
    where
    lemma :
      ∀ b → b ≡ p 0 →
      ∃ λ n → T (p n) × ∀ m → m < n → ¬ T (p m)
    lemma true  eq = 0 , subst T eq _ , λ _ ()
    lemma false eq =
      case ∃→∃-least {p = p ∘→ 1+} ok of λ {
        (n , ok , least) →
        1+ n
      , ok
      , (λ where
           0 _ →
             T (p 0)  →⟨ subst T (sym eq) ⟩
             ⊥        □
           (1+ m) 1+m<1+n →
             T (p (1+ m))  →⟨ least m (+-cancelˡ-< 1 m n 1+m<1+n) ⟩
             ⊥             □) }

-- Is-proposition is closed under ∃-least (assuming function
-- extensionality).

∃-least-propositional :
  ∀ {p} {P : ℕ → Set p} →
  Function-extensionality lzero p →
  Function-extensionality p lzero →
  (∀ n → Is-proposition (P n)) →
  Is-proposition (∃-least P)
∃-least-propositional
  fe₁ fe₂ P-prop
  {x = n₁ , p₁ , least₁}
  {y = n₂ , p₂ , least₂} =
  case n₁≡n₂ of λ {
    refl →
  cong₂ (λ p least → _ , p , least)
    (P-prop _)
    (Is-proposition-Π fe₁ λ _ →
     Is-proposition-Π fe₁ λ _ →
     Is-proposition-Π fe₂ λ _ →
     ⊥-propositional) }
  where
  n₁≡n₂ : n₁ ≡ n₂
  n₁≡n₂ = case <-cmp n₁ n₂ of λ where
    (tri< n₁<n₂ _     _)     → ⊥-elim (least₂ _ n₁<n₂ p₁)
    (tri≈ _     n₁≡n₂ _)     → n₁≡n₂
    (tri> _     _     n₁>n₂) → ⊥-elim (least₁ _ n₁>n₂ p₂)

opaque

  -- The relation _<′_ is transitive.

  <′-trans : m <′ n → n <′ o → m <′ o
  <′-trans p q = ≤⇒≤′ (<-trans (<′⇒< p) (<′⇒< q))

opaque

  -- The relation _<′_ is contained in _≤′_.

  <′→≤′ : m <′ n → m ≤′ n
  <′→≤′ = ≤⇒≤′ ∘→ <⇒≤ ∘→ <′⇒<

opaque

  -- Zero is the least natural number.

  0≤′ : 0 ≤′ n
  0≤′ = ≤⇒≤′ z≤n

opaque

  -- The number m is bounded by the maximum of m and n.

  ≤′⊔ʳ : m ≤′ m ⊔ n
  ≤′⊔ʳ = ≤⇒≤′ (m≤m⊔n _ _)

opaque

  -- The number n is bounded by the maximum of m and n.

  ≤′⊔ˡ : n ≤′ m ⊔ n
  ≤′⊔ˡ = ≤⇒≤′ (m≤n⊔m _ _)

opaque

  -- The function _⊔_ is monotone.

  ⊔-mono : m ≤′ m′ → n ≤′ n′ → m ⊔ n ≤′ m′ ⊔ n′
  ⊔-mono p q = ≤⇒≤′ (⊔-mono-≤ (≤′⇒≤ p) (≤′⇒≤ q))

opaque

  -- "Reflexivity" of _==_

  ==-refl : ∀ n → (n == n) ≡ true
  ==-refl 0 = refl
  ==-refl (1+ n) = ==-refl n

opaque

  -- "Symmetry" of _==_

  ==-sym : ∀ m n → (m == n) ≡ (n == m)
  ==-sym zero zero = refl
  ==-sym zero (1+ n) = refl
  ==-sym (1+ m) zero = refl
  ==-sym (1+ m) (1+ n) = ==-sym m n

opaque

  -- If m < n then n == m ≡ false

  <⇒¬== : m < n → (n == m) ≡ false
  <⇒¬==            {n = 0}    ()
  <⇒¬== {m = 0}    {n = 1+ _} m<n       = refl
  <⇒¬== {m = 1+ _} {n = 1+ _} (s≤s m<n) = <⇒¬== m<n

opaque

  -- A "preservation" property for _==_ under subtraction

  <⇒==∸ : k ≤ m → k ≤ n → (m == n) ≡ (m ∸ k == n ∸ k)
  <⇒==∸ {(zero)} k<m k<n = refl
  <⇒==∸ {1+ k} (s≤s k<m) (s≤s k<n) = <⇒==∸ k<m k<n

-- Infinite sequences of elements of a given type as functions from Nat

Sequence : (A : Set a) → Set a
Sequence A = Nat → A

opaque

  -- Multiplication respects greatest lower bounds of sequences
  -- of natural numbers

  *-LUB :
    (nᵢ : Sequence Nat) →
    (∀ i → nᵢ i ≤ n) →
    (∀ m → (∀ i → nᵢ i ≤ m) → n ≤ m) →
    (∀ i → k * nᵢ i ≤ k * n) ×
    (∀ m → (∀ i → k * nᵢ i ≤ m) → k * n ≤ m)
  *-LUB {n} {k = 0} nᵢ ≤n n-lub =
    (λ _ → ≤-refl) , (λ _ _ → z≤n)
  *-LUB {n} {k = 1+ k} nᵢ ≤n n-lub =
    (λ i → *-monoʳ-≤ (1+ k) (≤n i)) ,
    λ m ≤m →
      let nᵢ≤ : ∀ i → nᵢ i ≤ m / (1+ k)
          nᵢ≤ i = begin
            nᵢ i                   ≡˘⟨ m*n/n≡m (nᵢ i) (1+ k) ⟩
            nᵢ i * (1+ k) / (1+ k) ≡⟨ /-congˡ (*-comm (nᵢ i) (1+ k)) ⟩
            (1+ k) * nᵢ i / (1+ k) ≤⟨ /-monoˡ-≤ (1+ k) (≤m i) ⟩
            m / 1+ k ∎
      in  begin
            (1+ k) * n            ≤⟨ *-monoʳ-≤ (1+ k) (n-lub _ nᵢ≤) ⟩
            (1+ k) * (m / 1+ k)   ≡⟨ *-comm (1+ k) (m / 1+ k) ⟩
            (m / (1+ k)) * (1+ k) ≤⟨ m/n*n≤m m (1+ k) ⟩
            m ∎
    where
    open ≤-Reasoning

opaque

  -- Addition respects greatest lower bounds of sequences
  -- of natural numbers

  +-LUB :
    (nᵢ : Sequence Nat) →
    (∀ i → nᵢ i ≤ n) →
    (∀ m → (∀ i → nᵢ i ≤ m) → n ≤ m) →
    (∀ i → k + nᵢ i ≤ k + n) ×
    (∀ m → (∀ i → k + nᵢ i ≤ m) → k + n ≤ m)
  +-LUB {n} {k} nᵢ ≤n n-lub =
    (λ i → +-monoʳ-≤ k (≤n i)) ,
    λ m ≤m →
      let nᵢ≤ : ∀ i → nᵢ i ≤ m ∸ k
          nᵢ≤ i = begin
            nᵢ i         ≡˘⟨ m+n∸m≡n k (nᵢ i) ⟩
            k + nᵢ i ∸ k ≤⟨ ∸-monoˡ-≤ k (≤m i) ⟩
            m ∸ k        ∎
      in  begin
            k + n       ≤⟨ +-monoʳ-≤ k (n-lub _ nᵢ≤) ⟩
            k + (m ∸ k) ≡⟨ m+[n∸m]≡n (m+n≤o⇒m≤o k (≤m 0)) ⟩
            m           ∎
    where
    open ≤-Reasoning

opaque

  -- Non-zero numbers are at least 1

  1≤n : n ≢ 0 → 1 ≤ n
  1≤n {(zero)} n≢0 = ⊥-elim (n≢0 refl)
  1≤n {1+ n} n≢0 = s≤s z≤n
