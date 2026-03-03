------------------------------------------------------------------------
-- Division
------------------------------------------------------------------------

import Graded.Modality

module Graded.Modality.Properties.Division
  {a} {M : Set a}
  (open Graded.Modality M)
  (𝕄 : Modality)
  where

open Modality 𝕄

open import Graded.Modality.Properties.Meet 𝕄
open import Graded.Modality.Properties.Multiplication 𝕄
open import Graded.Modality.Properties.PartialOrder 𝕄

open import Tools.Empty
open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum using (_⊎_; inj₁; inj₂)

private variable
  p p₁ p₂ q q₁ q₂ r r₁ r₂ : M

------------------------------------------------------------------------
-- The relation _/_≡_

-- The relation p / q ≤ r is inhabited if "p divided by q" is bounded
-- by r.

infix 4 _/_≤_

_/_≤_ : M → M → M → Set a
p / q ≤ r = p ≤ q · r

-- The relation p / q ≡ r is inhabited if r is the least value for
-- which p / q ≤_ is inhabited.

infix 4 _/_≡_

_/_≡_ : M → M → M → Set a
p / q ≡ r = Least-such-that (p / q ≤_) r

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
   ∃ (Least-such-that P)) →
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

-- Division is monotone in its first argument.

/-monotoneˡ :
  p₁ / q ≡ r₁ → p₂ / q ≡ r₂ → p₁ ≤ p₂ → r₁ ≤ r₂
/-monotoneˡ
  {p₁ = p₁} {q = q} {p₂ = p₂} {r₂ = r₂}
  (_ , r₁≤) (p₂/q≤r₂ , _) p₁≤p₂ =
  r₁≤ _ $ begin
    p₁      ≤⟨ p₁≤p₂ ⟩
    p₂      ≤⟨ p₂/q≤r₂ ⟩
    q · r₂  ∎
  where
  open Tools.Reasoning.PartialOrder ≤-poset

-- Division is antitone in its second argument.

/-antitoneʳ :
  p / q₁ ≡ r₁ → p / q₂ ≡ r₂ → q₁ ≤ q₂ → r₂ ≤ r₁
/-antitoneʳ
  {p = p} {q₁ = q₁} {r₁ = r₁} {q₂ = q₂}
  (p/q₁≤r₁ , _) (_ , r₂≤) q₁≤q₂ =
  r₂≤ _ $ begin
    p        ≤⟨ p/q₁≤r₁ ⟩
    q₁ · r₁  ≤⟨ ·-monotoneˡ q₁≤q₂ ⟩
    q₂ · r₁  ∎
  where
  open Tools.Reasoning.PartialOrder ≤-poset

-- Division is decreasing if 𝟙 is the least value.

/-decreasing :
  (∀ p → 𝟙 ≤ p) →
  p / q ≡ r → r ≤ p
/-decreasing {p = p} {q = q} {r = r} 𝟙≤ =
  (p / q ≤ r) × (∀ r′ → p / q ≤ r′ → r ≤ r′)  →⟨ (_$ _) ∘→ proj₂ ⟩
  (p ≤ q · p → r ≤ p)                         ≡⟨ cong (λ p → p ≤ q · _ → _ ≤ _) (sym (·-identityˡ _)) ⟩→
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

-- The value of 𝟘 divided by p is 𝟘 if p is not equal to 𝟘 and the
-- zero-product property holds.

𝟘/≡𝟘 :
  (∀ {p q} → p · q ≡ 𝟘 → p ≡ 𝟘 ⊎ q ≡ 𝟘) →
  p ≢ 𝟘 → 𝟘 / p ≡ 𝟘
𝟘/≡𝟘 {p = p} zero-product p≢𝟘 = ≡·→/≡
  (λ q →
     p · 𝟘 ≡ p · q  →⟨ trans (sym (·-zeroʳ _)) ⟩
     𝟘 ≡ p · q      →⟨ zero-product ∘→ sym ⟩
     p ≡ 𝟘 ⊎ q ≡ 𝟘  →⟨ (λ { (inj₁ p≡𝟘) → ⊥-elim (p≢𝟘 p≡𝟘); (inj₂ q≡𝟘) → sym q≡𝟘 }) ⟩
     𝟘 ≡ q          □)
  (begin
     𝟘      ≡˘⟨ ·-zeroʳ _ ⟩
     p · 𝟘  ∎)
  where
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

------------------------------------------------------------------------
-- The predicate Supports-division-by

-- The property of supporting division by a given value.

Supports-division-by : M → Set a
Supports-division-by q =
  ∃ λ (_/q : M → M) → ∀ p r → (p /q) ≤ r ⇔ p ≤ q · r

-- The property of supporting division.

Supports-division : Set a
Supports-division = ∀ p → Supports-division-by p

-- "𝕄 supports division by q" is logically equivalent to "for all p
-- there is an r such that p / q ≡ r".

Supports-division-by⇔ :
  Supports-division-by q ⇔ (∀ p → ∃ λ r → p / q ≡ r)
Supports-division-by⇔ {q = q} =
    (λ (_/q , conn) p →
         (p /q)
       , (begin
            p           ≤⟨ conn p (p /q) .proj₁ ≤-refl ⟩
            q · (p /q)  ∎)
       , (λ r →
            (p / q ≤ r)  →⟨ conn p r .proj₂ ⟩
            (p /q) ≤ r   □))
  , (λ div →
         proj₁ ∘→ div
       , (λ p r →
              (λ p/q≤r → begin
                   p                 ≤⟨ div p .proj₂ .proj₁ ⟩
                   q · div p .proj₁  ≤⟨ ·-monotoneʳ p/q≤r ⟩
                   q · r             ∎)
            , div p .proj₂ .proj₂ _))
  where
  open Tools.Reasoning.PartialOrder ≤-poset

-- If 𝕄 supports division by q, then "p / q" is the least r such that
-- p ≤ q · r.

/-least-≤· :
  ((_/q , _) : Supports-division-by q) →
  Least-such-that (λ r → p ≤ q · r) (p /q)
/-least-≤· s = div _ .proj₂
  where
  div = Supports-division-by⇔ .proj₁ s

-- If 𝕄 supports division by q, then p / q ≡ r is logically equivalent
-- to "p / q is equal to r".

/≡⇔/≡ :
  ((_/q , _) : Supports-division-by q) →
  (p / q ≡ r) ⇔ (p /q) ≡ r
/≡⇔/≡ s =
    /≡-functional (/-least-≤· s)
  , (λ { refl → /-least-≤· s })

-- If 𝕄 supports division by q, then the associated division operation
-- is monotone.

/-monotoneˡ′ :
  ((_/q , _) : Supports-division-by q) →
  ∀ p₁ p₂ → p₁ ≤ p₂ → (p₁ /q) ≤ (p₂ /q)
/-monotoneˡ′ s p₁ p₂ = /-monotoneˡ (div p₁ .proj₂) (div p₂ .proj₂)
  where
  div = Supports-division-by⇔ .proj₁ s

-- Division by 𝟙 is supported, and the value of p divided by 𝟙 is p.

/𝟙≡′ : ∃ λ ((_/𝟙 , _) : Supports-division-by 𝟙) → (p /𝟙) ≡ p
/𝟙≡′ =
    Supports-division-by⇔ .proj₂ (λ _ → _ , /𝟙≡)
  , refl

-- If 𝟙 is the least value and 𝟘 the greatest one, then division by 𝟘
-- is supported and the value of p divided by 𝟘 is 𝟙.

/𝟘≡𝟙′ :
  (∀ p → 𝟙 ≤ p) → (∀ p → p ≤ 𝟘) →
  (∃ λ ((_/𝟘 , _) : Supports-division-by 𝟘) → (p /𝟘) ≡ 𝟙)
/𝟘≡𝟙′ 𝟙≤ ≤𝟘 =
    Supports-division-by⇔ .proj₂ (λ _ → _ , /𝟘≡𝟙 𝟙≤ (≤𝟘 _))
  , refl

-- If 𝟙 is the least value and division by p is supported, then the
-- value of p divided by p is 𝟙.

/≡𝟙′ :
  (∀ p → 𝟙 ≤ p) →
  ((_/p , _) : Supports-division-by p) →
  (p /p) ≡ 𝟙
/≡𝟙′ 𝟙≤ div = /≡⇔/≡ div .proj₁ (/≡𝟙 𝟙≤)

-- If 𝟙 is the least value and division by p is supported, then the
-- value of 𝟙 divided by p is 𝟙.

𝟙/≡𝟙′ :
  (∀ p → 𝟙 ≤ p) →
  ((_/p , _) : Supports-division-by p) →
  (𝟙 /p) ≡ 𝟙
𝟙/≡𝟙′ 𝟙≤ div = /≡⇔/≡ div .proj₁ (𝟙/≡𝟙 𝟙≤)

-- If the zero-product property holds, division by p is supported, and
-- p is not 𝟘, then the value of 𝟘 divided by p is 𝟘.

𝟘/≡𝟘′ :
  (∀ {p q} → p · q ≡ 𝟘 → p ≡ 𝟘 ⊎ q ≡ 𝟘) →
  ((_/p , _) : Supports-division-by p) →
  p ≢ 𝟘 → (𝟘 /p) ≡ 𝟘
𝟘/≡𝟘′ zero-product div p≢𝟘 =
  /≡⇔/≡ div .proj₁ (𝟘/≡𝟘 zero-product p≢𝟘)
