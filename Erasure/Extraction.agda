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
erase U = undefined
erase (Π p , q ▷ F ▹ G) = undefined
erase (U.lam p t) = T.lam (erase t)
erase (t ∘⟨ 𝟘 ⟩ u) = erase t T.∘ undefined
erase (t ∘⟨ ω ⟩ u) = erase t T.∘ erase u
erase (Σ _ , _ ▷ _ ▹ _) = undefined
erase (U.prod _ 𝟘 _ u) = erase u
erase (U.prod _ ω t u) = T.prod (erase t) (erase u)
erase (U.fst 𝟘 _) = undefined
erase (U.fst ω t) = T.fst (erase t)
erase (U.snd 𝟘 t) = erase t
erase (U.snd ω t) = T.snd (erase t)
erase (U.prodrec 𝟘 _ _ _ u) = erase u T.[ undefined , undefined ]
erase (U.prodrec ω 𝟘 _ t u) = T.lam (erase u) T.[ undefined ] T.∘
                              erase t
erase (U.prodrec ω ω _ t u) = T.prodrec (erase t) (erase u)
erase ℕ = undefined
erase U.zero = T.zero
erase (U.suc t) = T.suc (erase t)
erase (U.natrec p r A z s n) = T.natrec (erase z) (erase s) (erase n)
erase Unit = undefined
erase U.star = T.star
erase Empty = undefined
erase (Emptyrec p A t) = undefined

eraseSubst : U.Subst m n → T.Subst m n
eraseSubst σ x = erase (σ x)

eraseWk : U.Wk m n → T.Wk m n
eraseWk id = id
eraseWk (step ρ) = step (eraseWk ρ)
eraseWk (lift ρ) = lift (eraseWk ρ)
