{-# OPTIONS --without-K --safe #-}

module Definition.Modality.Properties where

open import Definition.Modality

open import Tools.Product
open import Tools.PropositionalEquality

private
  variable
    M : Set
    𝕄 : Modality M
    p q : M

≤-reflexive : {𝕄 : Modality M} {p : M} → Modality._≤_ 𝕄 p p
≤-reflexive {𝕄 = 𝕄} {p} = sym (Modality.∧-Idempotent 𝕄 p)

≤-transitive : {𝕄 : Modality M} {p q r : M}
             → Modality._≤_ 𝕄 p q → Modality._≤_ 𝕄 q r
             → Modality._≤_ 𝕄 p r
≤-transitive {𝕄 = 𝕄} {p} {q} {r} x y = subst₂ _≡_
  (subst (_≡ p) (cong₂ (Modality._∧_ 𝕄) refl y) (sym x))
  (cong₂ (Modality._∧_ 𝕄) (sym x) refl)
  (sym (Modality.∧-Associative 𝕄 p q r))

≤-antisymmetric : {𝕄 : Modality M} {p q : M} → Modality._≤_ 𝕄 p q
                → Modality._≤_ 𝕄 q p → p ≡ q
≤-antisymmetric {𝕄 = 𝕄} {p} {q} x y = subst₂ _≡_
  (subst (_≡ p) (Modality.∧-Commutative 𝕄 p q) (sym x))
  (sym y)
  refl

+-monotone : {𝕄 : Modality M} {p q r : M}
           → Modality._≤_ 𝕄 p q 
           → Modality._≤_ 𝕄 (Modality._+_ 𝕄 p r) (Modality._+_ 𝕄 q r)
+-monotone {𝕄 = 𝕄} {p} {q} {r} x = subst₂ _≡_
  (cong₂ (Modality._+_ 𝕄) (sym x) refl)
  (proj₂ (Modality.+Distr∧ 𝕄) r p q)
  refl

+-monotone₂ : {𝕄 : Modality M} {p p′ q q′ : M}
            → Modality._≤_ 𝕄 p p′
            → Modality._≤_ 𝕄 q q′
            → Modality._≤_ 𝕄 (Modality._+_ 𝕄 p q) (Modality._+_ 𝕄 p′ q′)
+-monotone₂ {𝕄 = 𝕄} {p = p} {p′} {q} {q′} x y = ≤-transitive {𝕄 = 𝕄}
            (+-monotone {𝕄 = 𝕄} x)
            (subst₂ (Modality._≤_ 𝕄)
                    (Modality.+-Commutative 𝕄 q p′)
                    (Modality.+-Commutative 𝕄 q′ p′)
                    (+-monotone {𝕄 = 𝕄} y)
            )

·-monotoneˡ : {𝕄 : Modality M} {p q r : M}
           → Modality._≤_ 𝕄 p q
           → Modality._≤_ 𝕄 (Modality._·_ 𝕄 r p) (Modality._·_ 𝕄 r q)
·-monotoneˡ {𝕄 = 𝕄} {p = p} {q} {r} x = subst₂ _≡_
  (cong₂ (Modality._·_ 𝕄) refl (sym x))
  (proj₁ (Modality.·Distr∧ 𝕄) r p q)
  refl

·-monotoneʳ : {𝕄 : Modality M} {p q r : M}
           → Modality._≤_ 𝕄 p q
           → Modality._≤_ 𝕄 (Modality._·_ 𝕄 p r) (Modality._·_ 𝕄 q r)
·-monotoneʳ {𝕄 = 𝕄} {p = p} {q} {r} x = subst₂ _≡_
  (cong₂ (Modality._·_ 𝕄) (sym x) refl)
  (proj₂ (Modality.·Distr∧ 𝕄) r p q)
  refl

·-monotone₂ : {𝕄 : Modality M} {p q p′ q′ : M}
            → Modality._≤_ 𝕄 p q → Modality._≤_ 𝕄 p′ q′
            → Modality._≤_ 𝕄 (Modality._·_ 𝕄 p p′) (Modality._·_ 𝕄 q q′)
·-monotone₂ {𝕄 = 𝕄} x y = ≤-transitive {𝕄 = 𝕄}
  (·-monotoneˡ {𝕄 = 𝕄} y)
  (·-monotoneʳ {𝕄 = 𝕄} x)
  
