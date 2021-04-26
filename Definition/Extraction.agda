module Definition.Extraction where

open import Definition.Typed
open import Definition.Modality.Erasure

open import Tools.Fin
open import Tools.Nat
open import Tools.PropositionalEquality

open import Definition.Untyped Erasure as U
open import Definition.Typed Erasure as Ty
open import Definition.Target as T

private
  variable
    m n : Nat

-- Transform a term from the source to the target language, erasing all erasable content.

erase : U.Term n → T.Term n
erase (var x)                                     = T.var x
erase (gen Ukind [])                              = T.Type
erase (gen (Pikind p q) (F ∷ G ∷ []))             = T.Type
erase (gen (Lamkind 𝟘) (t ∷ []))                  = T.subst drop (erase t)
erase (gen (Lamkind ω) (t ∷ []))                  = T.lam (erase t)
erase (gen (Appkind 𝟘) (t ∷ u ∷ []))              = erase t
erase (gen (Appkind ω) (t ∷ u ∷ []))              = (erase t) ∘ (erase u)
erase (gen (Sigmakind p) (F ∷ G ∷ []))            = T.Type
erase (gen Prodkind (t ∷ u ∷ []))                 = T.prod (erase t) (erase u)
erase (gen Fstkind (t ∷ []))                      = T.fst (erase t)
erase (gen Sndkind (t ∷ []))                      = T.snd (erase t)
erase (gen (Prodreckind 𝟘) (A ∷ t ∷ u ∷ []))      = T.subst drop (T.subst drop (erase u))
erase (gen (Prodreckind ω) (A ∷ t ∷ u ∷ []))      = Term.prodrec (erase t) (erase u)
erase (gen Natkind [])                            = T.Type
erase (gen Zerokind [])                           = T.zero
erase (gen Suckind (t ∷ []))                      = T.suc (erase t)
erase (gen (Natreckind p r) (A ∷ z ∷ s ∷ n ∷ [])) = T.natrec (erase z) (erase s) (erase n)
erase (gen Unitkind [])                           = T.Type
erase (gen Starkind [])                           = T.star
erase (gen Emptykind [])                          = T.Type
erase (gen (Emptyreckind p) (A ∷ t ∷ []))         = undefined (erase t)

-- Transform a substitution from the source to the target language, erasing all erasable content.

eraseSubst : U.Subst m n → T.Subst m n
eraseSubst σ x = erase (σ x)
