{-# OPTIONS --without-K --safe #-}

module Definition.Modality.Properties where

open import Definition.Modality

open import Tools.Product
open import Tools.PropositionalEquality

private
  variable
    M : Set
    𝕄 : Modality M
    p p′ q q′ r : M

-- ≤ is reflexive
-- p ≤ p

≤-reflexive : Modality._≤_ 𝕄 p p
≤-reflexive {𝕄 = 𝕄} {p} = sym (Modality.∧-Idempotent 𝕄 p)

-- ≤ is transitive
-- If p ≤ q and q ≤ r then p ≤ r

≤-transitive : Modality._≤_ 𝕄 p q → Modality._≤_ 𝕄 q r → Modality._≤_ 𝕄 p r
≤-transitive {𝕄 = 𝕄} {p} {q} {r} x y = subst₂ _≡_
  (subst (_≡ p) (cong₂ (Modality._∧_ 𝕄) refl y) (sym x))
  (cong₂ (Modality._∧_ 𝕄) (sym x) refl)
  (sym (Modality.∧-Associative 𝕄 p q r))

-- ≤ is antisymmetric
-- If p ≤ q and q ≤ p then p ≡ q

≤-antisymmetric : Modality._≤_ 𝕄 p q → Modality._≤_ 𝕄 q p → p ≡ q
≤-antisymmetric {𝕄 = 𝕄} {p} {q} x y = subst₂ _≡_
  (subst (_≡ p) (Modality.∧-Commutative 𝕄 p q) (sym x))
  (sym y)
  refl

-- Addition on the left is a monotone function
-- If p ≤ q then p + r ≤ q + r

+-monotoneˡ : Modality._≤_ 𝕄 p q → Modality._≤_ 𝕄 (Modality._+_ 𝕄 p r) (Modality._+_ 𝕄 q r)
+-monotoneˡ {𝕄 = 𝕄} {p} {q} {r} p≤q = subst₂ _≡_
  (cong₂ (Modality._+_ 𝕄) (sym p≤q) refl)
  (proj₂ (Modality.+Distr∧ 𝕄) r p q)
  refl

-- Addition on the right is a monotone function
-- If p ≤ q then r + p ≤ r + q

+-monotoneʳ : Modality._≤_ 𝕄 p q → Modality._≤_ 𝕄 (Modality._+_ 𝕄 r p) (Modality._+_ 𝕄 r q)
+-monotoneʳ {𝕄 = 𝕄} {p} {q} {r} p≤q = subst₂ _≡_
  (cong₂ (Modality._+_ 𝕄) refl (sym p≤q))
  (proj₁ (Modality.+Distr∧ 𝕄) r p q)
  refl

-- Addition is a monotone function
-- If p ≤ p′ and q ≤ q′ then p + q ≤ p′ + q′

+-monotone : Modality._≤_ 𝕄 p p′ → Modality._≤_ 𝕄 q q′
           → Modality._≤_ 𝕄 (Modality._+_ 𝕄 p q) (Modality._+_ 𝕄 p′ q′)
+-monotone {𝕄 = 𝕄} p≤p′ q≤q′ = ≤-transitive {𝕄 = 𝕄}
            (+-monotoneˡ {𝕄 = 𝕄} p≤p′)
            (+-monotoneʳ {𝕄 = 𝕄} q≤q′)

-- Meet on the left is a monotone function
-- If p ≤ q then p ∧ r ≤ q ∧ r

∧-monotoneˡ : Modality._≤_ 𝕄 p q
            → Modality._≤_ 𝕄 (Modality._∧_ 𝕄 p r) (Modality._∧_ 𝕄 q r)
∧-monotoneˡ {𝕄 = 𝕄} {p} {q} {r} p≤q = begin
  Modality._∧_ 𝕄 p r
    ≡⟨ cong₂ (Modality._∧_ 𝕄) p≤q (sym (Modality.∧-Idempotent 𝕄 r)) ⟩
  (𝕄 Modality.∧ ((𝕄 Modality.∧ p) q)) (Modality._∧_ 𝕄 r r)
    ≡⟨ Modality.∧-Associative 𝕄 p q (Modality._∧_ 𝕄 r r) ⟩
  (𝕄 Modality.∧ p) ((𝕄 Modality.∧ q) ((𝕄 Modality.∧ r) r))
    ≡⟨ cong₂ (Modality._∧_ 𝕄) refl (Modality.∧-Commutative 𝕄 q (Modality._∧_ 𝕄 r r)) ⟩
   Modality._∧_ 𝕄 p (Modality._∧_ 𝕄 (Modality._∧_ 𝕄 r r) q)
     ≡⟨ cong₂ (Modality._∧_ 𝕄) refl (Modality.∧-Associative 𝕄 r r q) ⟩
   Modality._∧_ 𝕄 p (Modality._∧_ 𝕄 r ((𝕄 Modality.∧ r) q))
     ≡⟨ sym (Modality.∧-Associative 𝕄 p r (Modality._∧_ 𝕄 r q)) ⟩
   Modality._∧_ 𝕄 (Modality._∧_ 𝕄 p r) (Modality._∧_ 𝕄 r q)
     ≡⟨ cong₂ (Modality._∧_ 𝕄) refl (Modality.∧-Commutative 𝕄 r q) ⟩
   (Modality._∧_ 𝕄  (Modality._∧_ 𝕄 p r) (Modality._∧_ 𝕄 q r)) ∎

-- Meet on the right is a monotone function
-- If p ≤ q then r ∧ p ≤ r ∧ q

∧-monotoneʳ : Modality._≤_ 𝕄 p q → Modality._≤_ 𝕄 (Modality._∧_ 𝕄 r p) (Modality._∧_ 𝕄 r q)
∧-monotoneʳ {𝕄 = 𝕄} {p} {q} {r} p≤q = begin
  Modality._∧_ 𝕄 r p
    ≡⟨ cong₂ (Modality._∧_ 𝕄) (sym (Modality.∧-Idempotent 𝕄 r)) p≤q ⟩
  Modality._∧_ 𝕄 (Modality._∧_ 𝕄 r r) (Modality._∧_ 𝕄 p q)
    ≡⟨ Modality.∧-Associative 𝕄 r r (Modality._∧_ 𝕄 p q) ⟩
  Modality._∧_ 𝕄 r (Modality._∧_ 𝕄 r (Modality._∧_ 𝕄 p q))
    ≡⟨ cong (𝕄 Modality.∧ r) (Modality.∧-Commutative 𝕄 r (Modality._∧_ 𝕄 p q)) ⟩
  Modality._∧_ 𝕄 r (Modality._∧_ 𝕄 (Modality._∧_ 𝕄 p q) r)
    ≡⟨ cong (𝕄 Modality.∧ r) (Modality.∧-Associative 𝕄 p q r) ⟩
  Modality._∧_ 𝕄 r (Modality._∧_ 𝕄 p (Modality._∧_ 𝕄 q r))
    ≡⟨ sym (Modality.∧-Associative 𝕄 r p ((𝕄 Modality.∧ q) r)) ⟩
  Modality._∧_ 𝕄 (Modality._∧_ 𝕄 r p) (Modality._∧_ 𝕄 q r)
    ≡⟨ cong₂ (Modality._∧_ 𝕄) refl (Modality.∧-Commutative 𝕄 q r) ⟩
  (Modality._∧_ 𝕄 (Modality._∧_ 𝕄 r p) (Modality._∧_ 𝕄 r q)) ∎

-- Meet is a monotone function
-- If p ≤ p′ and q ≤ q′ then p ∧ p′ ≤ q ∧ q′

∧-monotone : Modality._≤_ 𝕄 p p′ → Modality._≤_ 𝕄 q q′
           → Modality._≤_ 𝕄 (Modality._∧_ 𝕄 p q) (Modality._∧_ 𝕄 p′ q′)
∧-monotone {𝕄 = 𝕄} p≤p′ q≤q′ = ≤-transitive {𝕄 = 𝕄}
  (∧-monotoneˡ {𝕄 = 𝕄} p≤p′)
  (∧-monotoneʳ {𝕄 = 𝕄} q≤q′)

-- Multiplication on the left is a monotone function
-- If p ≤ q then p · r ≤ q · r

·-monotoneˡ : Modality._≤_ 𝕄 p q
            → Modality._≤_ 𝕄 (Modality._·_ 𝕄 p r) (Modality._·_ 𝕄 q r)
·-monotoneˡ {𝕄 = 𝕄} {p = p} {q} {r} p≤q = subst₂ _≡_
  (cong₂ (Modality._·_ 𝕄) (sym p≤q) refl)
  (proj₂ (Modality.·Distr∧ 𝕄) r p q)
  refl

-- Multiplication on the right is a monotone function
-- If p ≤ q then r · p ≤ r · q

·-monotoneʳ : Modality._≤_ 𝕄 p q
            → Modality._≤_ 𝕄 (Modality._·_ 𝕄 r p) (Modality._·_ 𝕄 r q)
·-monotoneʳ {𝕄 = 𝕄} {p = p} {q} {r} p≤q = subst₂ _≡_
  (cong₂ (Modality._·_ 𝕄) refl (sym p≤q))
  (proj₁ (Modality.·Distr∧ 𝕄) r p q)
  refl

-- Multiplication is a monotone function
-- If p ≤ p′ and q ≤ q′ then p · p′ ≤ q · q′

·-monotone : Modality._≤_ 𝕄 p p′ → Modality._≤_ 𝕄 q q′
           → Modality._≤_ 𝕄 (Modality._·_ 𝕄 p q) (Modality._·_ 𝕄 p′ q′)
·-monotone {𝕄 = 𝕄} p≤p′ q≤q′ = ≤-transitive {𝕄 = 𝕄}
  (·-monotoneˡ {𝕄 = 𝕄} p≤p′)
  (·-monotoneʳ {𝕄 = 𝕄} q≤q′)
