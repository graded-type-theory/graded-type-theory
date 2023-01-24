{-# OPTIONS --without-K --safe #-}

open import Tools.Relation

module Definition.Untyped.BindingType {a ℓ} (M′ : Setoid a ℓ) where

open Setoid M′ using (_≈_) renaming (Carrier to M)

open import Tools.Level
open import Definition.Untyped M


private
  variable
    p p′ q q′ : M
    m : SigmaMode


-- (Modal) Equality of BindingType
data _≋_ : (W W′ : BindingType) → Set (a ⊔ ℓ) where
  Π≋Π : (p≈p′ : p ≈ p′) → (q≈q′ : q ≈ q′) → BΠ p q ≋ BΠ p′ q′
  Σ≋Σ : (q≈q′ : q ≈ q′)                   → BΣ m q ≋ BΣ m q′

refl : Reflexive _≋_
refl {BΠ p q} = Π≋Π (Setoid.refl M′) (Setoid.refl M′)
refl {BΣ _ q} = Σ≋Σ (Setoid.refl M′)

sym : Symmetric _≋_
sym (Π≋Π p≈p′ q≈q′) = Π≋Π (Setoid.sym M′ p≈p′) (Setoid.sym M′ q≈q′)
sym (Σ≋Σ q≈q′)      = Σ≋Σ (Setoid.sym M′ q≈q′)

trans : Transitive _≋_
trans (Π≋Π p≈p′ q≈q′) (Π≋Π p′≈p″ q′≈q″) = Π≋Π (Setoid.trans M′ p≈p′ p′≈p″)
                                              (Setoid.trans M′ q≈q′ q′≈q″)
trans (Σ≋Σ q≈q′)      (Σ≋Σ q′≈q″)       = Σ≋Σ (Setoid.trans M′ q≈q′ q′≈q″)

isEquivalence : IsEquivalence _≋_
isEquivalence = record { refl = refl ; sym = sym ; trans = trans }
