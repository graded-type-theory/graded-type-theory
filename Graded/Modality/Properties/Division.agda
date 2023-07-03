------------------------------------------------------------------------
-- Division
------------------------------------------------------------------------

import Graded.Modality

module Graded.Modality.Properties.Division
  {a} {M : Set a}
  (open Graded.Modality M)
  (𝕄 : Semiring-with-meet)
  where

open Semiring-with-meet 𝕄

open import Graded.Modality.Properties.Meet 𝕄
open import Graded.Modality.Properties.Multiplication 𝕄
open import Graded.Modality.Properties.PartialOrder 𝕄

open import Tools.Function
open import Tools.Nullary
open import Tools.Product
open import Tools.PropositionalEquality
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum using (_⊎_; inj₁; inj₂)

private variable
  p q r r₁ r₂ : M

-- The relation p / q ≤ r is inhabited if "p divided by q" is bounded
-- by r.

infix 4 _/_≤_

_/_≤_ : M → M → M → Set a
p / q ≤ r = p ≤ q · r

-- The relation p / q ≡ r is inhabited if r is the least value for
-- which p / q ≤_ is inhabited.

infix 4 _/_≡_

_/_≡_ : M → M → M → Set a
p / q ≡ r = p / q ≤ r × (∀ r′ → p / q ≤ r′ → r ≤ r′)

-- The relation _/_≤_ is total if 𝟘 is the greatest value.

/≤-total : (∀ p → p ≤ 𝟘) → ∃ (p / q ≤_)
/≤-total {p = p} {q = q} ≤𝟘 =
    𝟘
  , (           $⟨ ≤𝟘 _ ⟩
     p ≤ 𝟘      ≡⟨ cong (_ ≤_) (sym (·-zeroʳ _)) ⟩→
     p ≤ q · 𝟘  →⟨ idᶠ ⟩
     p / q ≤ 𝟘  □)

-- The relation _/_≡_ is total if equality is decidable, 𝟘 is the
-- greatest value, and all "decidable subsets" that contain 𝟘 and are
-- closed under _∧_ have a least value.

/≡-total :
  Decidable (_≡_ {A = M}) →
  (∀ p → p ≤ 𝟘) →
  ((P : M → Set a) → (∀ p → Dec (P p)) →
   P 𝟘 → (∀ p q → P p → P q → P (p ∧ q)) →
   ∃ λ p → P p × (∀ q → P q → p ≤ q)) →
  ∃ (p / q ≡_)
/≡-total {p = p} {q = q} dec ≤𝟘 limit =
  limit (p / q ≤_) p/q≤? (/≤-total ≤𝟘 .proj₂) lemma
  where
  p/q≤? : ∀ r → Dec (p / q ≤ r)
  p/q≤? _ = ≡-decidable→≤-decidable dec _ _

  lemma :
    (r₁ r₂ : M) →
    p / q ≤ r₁ → p / q ≤ r₂ → p / q ≤ r₁ ∧ r₂
  lemma r₁ r₂ p/q≤r₁ p/q≤r₂ = begin
    p                ≤⟨ ∧-greatest-lower-bound p/q≤r₁ p/q≤r₂ ⟩
    q · r₁ ∧ q · r₂  ≡˘⟨ ·-distribˡ-∧ _ _ _ ⟩
    q · (r₁ ∧ r₂)    ∎
    where
    open Tools.Reasoning.PartialOrder ≤-poset

-- The relation _/_≡_ is functional.

/≡-functional : p / q ≡ r₁ → p / q ≡ r₂ → r₁ ≡ r₂
/≡-functional (p/q≤r₁ , least₁) (p/q≤r₂ , least₂) =
  ≤-antisym (least₁ _ p/q≤r₂) (least₂ _ p/q≤r₁)

-- Division is decreasing if 𝟙 is the least value.

division-decreasing :
  (∀ p → 𝟙 ≤ p) →
  p / q ≡ r → r ≤ p
division-decreasing {p = p} {q = q} {r = r} 𝟙≤ =
  (p / q ≤ r) × (∀ r′ → p / q ≤ r′ → r ≤ r′)  →⟨ (_$ _) ∘→ proj₂ ⟩
  (p ≤ q · p → r ≤ p)                         ≡⟨ cong (λ p → p ≤ q · _ → _) (sym (·-identityˡ _)) ⟩→
  (𝟙 · p ≤ q · p → r ≤ p)                     →⟨ _$ ·-monotoneˡ (𝟙≤ _) ⟩
  r ≤ p                                       □

-- If q ·_ is injective "for r", then p / q ≡ r holds if p is equal to
-- q · r.

≡·→/≡ :
  (∀ p → q · r ≡ q · p → r ≡ p) →
  p ≡ q · r → p / q ≡ r
≡·→/≡ {q = q} {r = r} {p = p} inj refl =
    ≤-refl
  , λ r′ →
      (q · r / q ≤ r′)        →⟨ idᶠ ⟩
      q · r ≤ q · r′          →⟨ idᶠ ⟩
      q · r ≡ q · r ∧ q · r′  →⟨ flip trans (sym (·-distribˡ-∧ _ _ _)) ⟩
      q · r ≡ q · (r ∧ r′)    →⟨ inj _ ⟩
      r ≡ r ∧ r′              →⟨ idᶠ ⟩
      r ≤ r′                  □

-- If q ·_ is split surjective "for p", then p / q ≡ r holds only if p
-- is equal to q · r.

/≡→≡· :
  (∃ λ r → p ≡ q · r) →
  p / q ≡ r → p ≡ q · r
/≡→≡· {p = p} {q = q} {r = r} surj (p≤qr , least) =
  ≤-antisym p≤qr $ begin
    q · r   ≤⟨ ·-monotoneʳ (least _ (≤-reflexive p≡qr′)) ⟩
    q · r′  ≡˘⟨ p≡qr′ ⟩
    p       ∎
  where
  open Tools.Reasoning.PartialOrder ≤-poset

  r′ = surj .proj₁

  p≡qr′ : p ≡ q · r′
  p≡qr′ = surj .proj₂

-- The value of p divided by 𝟙 is p.

/𝟙≡ : p / 𝟙 ≡ p
/𝟙≡ {p = p} = ≡·→/≡
  (λ q →
     𝟙 · p ≡ 𝟙 · q  →⟨ flip trans (·-identityˡ _) ⟩
     𝟙 · p ≡ q      →⟨ trans (sym (·-identityˡ _)) ⟩
     p ≡ q          □)
  (begin
     p      ≡˘⟨ ·-identityˡ _ ⟩
     𝟙 · p  ∎)
  where
  open Tools.Reasoning.PropositionalEquality

-- The value of p divided by p is 𝟙 if 𝟙 is the least value.

/≡𝟙 : (∀ p → 𝟙 ≤ p) → p / p ≡ 𝟙
/≡𝟙 {p = p} 𝟙≤ =
    (begin
       p      ≡˘⟨ ·-identityʳ _ ⟩
       p · 𝟙  ∎)
  , (λ q _ → begin
       𝟙  ≤⟨ 𝟙≤ _ ⟩
       q  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤-poset

-- The value of 𝟘 divided by p is 𝟘 if p is not equal to 𝟘 and 𝕄 has a
-- well-behaved zero.

𝟘/≡𝟘 : Has-well-behaved-zero 𝕄 → p ≢ 𝟘 → 𝟘 / p ≡ 𝟘
𝟘/≡𝟘 {p = p} well-behaved p≢𝟘 = ≡·→/≡
  (λ q →
     p · 𝟘 ≡ p · q  →⟨ trans (sym (·-zeroʳ _)) ⟩
     𝟘 ≡ p · q      →⟨ zero-product ∘→ sym ⟩
     p ≡ 𝟘 ⊎ q ≡ 𝟘  →⟨ (λ { (inj₁ p≡𝟘) → ⊥-elim (p≢𝟘 p≡𝟘); (inj₂ q≡𝟘) → sym q≡𝟘 }) ⟩
     𝟘 ≡ q          □)
  (begin
     𝟘      ≡˘⟨ ·-zeroʳ _ ⟩
     p · 𝟘  ∎)
  where
  open Has-well-behaved-zero well-behaved
  open Tools.Reasoning.PropositionalEquality

-- The value of p divided by 𝟘 is 𝟙 if p ≤ 𝟘 and 𝟙 is the least value.

/𝟘≡𝟙 : (∀ p → 𝟙 ≤ p) → p ≤ 𝟘 → p / 𝟘 ≡ 𝟙
/𝟘≡𝟙 {p = p} 𝟙≤ p≤𝟘 =
    (           $⟨ p≤𝟘 ⟩
     p ≤ 𝟘      ≡⟨ cong (_ ≤_) (sym (·-zeroˡ _)) ⟩→
     p ≤ 𝟘 · 𝟙  →⟨ idᶠ ⟩
     p / 𝟘 ≤ 𝟙  □)
  , (λ q _ → begin
       𝟙  ≤⟨ 𝟙≤ _ ⟩
       q  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤-poset

-- The value of 𝟙 divided by p is 𝟙 if 𝟙 is the least value.

𝟙/≡𝟙 : (∀ p → 𝟙 ≤ p) → 𝟙 / p ≡ 𝟙
𝟙/≡𝟙 {p = p} 𝟙≤ =
    (           $⟨ 𝟙≤ _ ⟩
     𝟙 ≤ p      ≡⟨ cong (_ ≤_) (sym (·-identityʳ _)) ⟩→
     𝟙 ≤ p · 𝟙  →⟨ idᶠ ⟩
     𝟙 / p ≤ 𝟙  □)
  , (λ q _ → begin
       𝟙  ≤⟨ 𝟙≤ _ ⟩
       q  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤-poset
