{-# OPTIONS --without-K --safe #-}
module Erasure.Extraction where

open import Definition.Modality.Instances.Erasure

open import Tools.Nat

open import Definition.Untyped Erasure as U
open import Erasure.Target as T

private
  variable
    m n : Nat
    Γ : Con U.Term n
    A t t′ u : U.Term n
    v v′ w : T.Term n
    p : Erasure


erase : U.Term n → T.Term n
erase (var x) = T.var x
erase U = ↯
erase (Π p , q ▷ F ▹ G) = ↯
erase (U.lam p t) = T.lam (erase t)
erase (t ∘⟨ 𝟘 ⟩ u) = erase t T.∘ ↯
erase (t ∘⟨ ω ⟩ u) = erase t T.∘ erase u
erase (Σ q ▷ F ▹ G) = ↯
erase (prod! t u) = T.prod (erase t) (erase u)
erase (U.fst t) = T.fst (erase t)
erase (U.snd t) = T.snd (erase t)
erase (U.prodrec 𝟘 q A t u) = T.prodrec (T.prod ↯ ↯) (erase u)
erase (U.prodrec ω q A t u) = T.prodrec (erase t) (erase u)
erase ℕ = ↯
erase U.zero = T.zero
erase (U.suc t) = T.suc (erase t)
erase (U.natrec p q r A z s n) = T.natrec (erase z) (erase s) (erase n)
erase Unit = ↯
erase U.star = T.star
erase Empty = ↯
erase (Emptyrec p A t) = ↯

eraseSubst : U.Subst m n → T.Subst m n
eraseSubst σ x = erase (σ x)

eraseWk : U.Wk m n → T.Wk m n
eraseWk id = id
eraseWk (step ρ) = step (eraseWk ρ)
eraseWk (lift ρ) = lift (eraseWk ρ)
