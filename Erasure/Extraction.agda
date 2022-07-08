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
erase (gen Ukind []) = undefined
erase (gen (Pikind p q) (F ∷ G ∷ [])) = undefined
erase (gen (Lamkind p) (t ∷ [])) = T.lam (erase t)
erase (gen (Appkind 𝟘) (t ∷ u ∷ [])) = erase t ∘ undefined
erase (gen (Appkind ω) (t ∷ u ∷ [])) = (erase t) ∘ (erase u)
erase (gen (Sigmakind p m) (F ∷ G ∷ [])) = undefined
erase (gen Prodkind (t ∷ u ∷ [])) = T.prod (erase t) (erase u)
erase (gen Fstkind (t ∷ [])) = T.fst (erase t)
erase (gen Sndkind (t ∷ [])) = T.snd (erase t)
erase (gen (Prodreckind 𝟘) (A ∷ t ∷ u ∷ [])) =
  (erase u) T.[ undefined , undefined ]
erase (gen (Prodreckind ω) (A ∷ t ∷ u ∷ [])) =
  Term.prodrec (erase t) (erase u)
erase (gen Natkind []) = undefined
erase (gen Zerokind []) = T.zero
erase (gen Suckind (t ∷ [])) = T.suc (erase t)
erase (gen (Natreckind p r) (A ∷ z ∷ s ∷ n ∷ [])) =
  T.natrec (erase z) (erase s) (erase n)
erase (gen Unitkind []) = undefined
erase (gen Starkind []) = T.star
erase (gen Emptykind []) = undefined
erase (gen (Emptyreckind p) (A ∷ t ∷ [])) = undefined

eraseSubst : U.Subst m n → T.Subst m n
eraseSubst σ x = erase (σ x)

eraseWk : U.Wk m n → T.Wk m n
eraseWk id = id
eraseWk (step ρ) = step (eraseWk ρ)
eraseWk (lift ρ) = lift (eraseWk ρ)
