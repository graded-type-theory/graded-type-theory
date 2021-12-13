{-# OPTIONS --without-K --safe #-}

module Tools.Fin where

open import Tools.Nat
open import Tools.Nullary
open import Tools.PropositionalEquality

open import Data.Fin.Base public using (Fin) renaming (zero to x0 ; suc to _+1)


-- Decidability of equality

_≟ⱽ_ : {n : Nat} → (x y : Fin n) → Dec (x ≡ y)
x0 ≟ⱽ x0 = yes refl
x0 ≟ⱽ (y +1) = no (λ ())
(x +1) ≟ⱽ x0 = no (λ ())
(x +1) ≟ⱽ (y +1) = map (cong _+1) (λ {refl → refl}) (x ≟ⱽ y)
