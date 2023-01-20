{-# OPTIONS --without-K --safe #-}

open import Tools.Relation
open import Definition.Modality

module Definition.Modality.Properties.Multiplication {a ℓ}
  {M′ : Setoid a ℓ}
  (𝕄 : ModalityWithout⊛ M′)
  where

open ModalityWithout⊛ 𝕄
open Setoid M′ renaming (Carrier to M)

open import Definition.Modality.Properties.PartialOrder 𝕄

open import Tools.Algebra M′
open import Tools.Nat hiding (_+_)
open import Tools.Product


private
  variable
    p p′ q q′ r r′ : M

-- Multiplication on the left is a monotone function
-- If p ≤ q then p · r ≤ q · r

·-monotoneˡ : p ≤ q → p · r ≤ q · r
·-monotoneˡ {p} {q} {r} p≤q = ≈-trans (·-congʳ p≤q) (·-distribʳ-∧ r p q)

-- Multiplication on the right is a monotone function
-- If p ≤ q then r · p ≤ r · q

·-monotoneʳ : p ≤ q → r · p ≤ r · q
·-monotoneʳ {p} {q} {r} p≤q = ≈-trans (·-congˡ p≤q) (·-distribˡ-∧ r p q)

-- Multiplication is a monotone function
-- If p ≤ p′ and q ≤ q′ then p · q ≤ p′ · q′

·-monotone : p ≤ p′ → q ≤ q′ → p · q ≤ p′ · q′
·-monotone p≤p′ q≤q′ = ≤-trans (·-monotoneˡ p≤p′) (·-monotoneʳ q≤q′)
