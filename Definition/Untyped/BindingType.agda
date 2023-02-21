module Definition.Untyped.BindingType {a} (M : Set a) where

open import Tools.Level
open import Tools.PropositionalEquality as PE
  using (_≈_; ≈-refl; ≈-sym; ≈-trans)
open import Tools.Relation

open import Definition.Untyped M


private
  variable
    p p′ q q′ : M
    m : SigmaMode


-- (Modal) Equality of BindingType
data _≋_ : (W W′ : BindingType) → Set a where
  Π≋Π : (p≈p′ : p ≈ p′) → (q≈q′ : q ≈ q′) → BΠ p q ≋ BΠ p′ q′
  Σ≋Σ : (q≈q′ : q ≈ q′)                   → BΣ m q ≋ BΣ m q′

refl : Reflexive _≋_
refl {BΠ p q} = Π≋Π ≈-refl ≈-refl
refl {BΣ _ q} = Σ≋Σ ≈-refl

sym : Symmetric _≋_
sym (Π≋Π p≈p′ q≈q′) = Π≋Π (≈-sym p≈p′) (≈-sym q≈q′)
sym (Σ≋Σ q≈q′)      = Σ≋Σ (≈-sym q≈q′)

trans : Transitive _≋_
trans (Π≋Π p≈p′ q≈q′) (Π≋Π p′≈p″ q′≈q″) = Π≋Π (≈-trans p≈p′ p′≈p″)
                                              (≈-trans q≈q′ q′≈q″)
trans (Σ≋Σ q≈q′)      (Σ≋Σ q′≈q″)       = Σ≋Σ (≈-trans q≈q′ q′≈q″)

isEquivalence : IsEquivalence _≋_
isEquivalence = record { refl = refl ; sym = sym ; trans = trans }
