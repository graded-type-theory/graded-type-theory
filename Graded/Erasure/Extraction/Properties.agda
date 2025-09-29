------------------------------------------------------------------------
-- Properties of the extraction function.
------------------------------------------------------------------------

open import Graded.Modality
open import Tools.PropositionalEquality as PE hiding (subst)

module Graded.Erasure.Extraction.Properties
  {a} {M : Set a}
  (𝕄 : Modality M)
  where

open Modality 𝕄

open import Graded.Modality.Nr-instances
open import Graded.Modality.Properties 𝕄

open import Graded.Erasure.Extraction 𝕄
open import Graded.Erasure.Target as T
  hiding (refl; trans)
open import Graded.Erasure.Target.Non-terminating
open import Graded.Erasure.Target.Properties

open import Definition.Untyped M as U
  hiding (Term; wk; _[_]; _[_,_]₁₀; liftSubst)
open import Definition.Untyped.Erased 𝕄 using (substᵉ; Jᵉ)
open import Definition.Untyped.Identity 𝕄 using (subst)
open import Definition.Untyped.Omega M as O using (Ω)
import Definition.Untyped.Properties M as UP

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
import Graded.Usage 𝕄 as MU
import Graded.Usage.Properties 𝕄 as MUP
import Graded.Usage.Properties.Has-well-behaved-zero 𝕄 as MUP𝟘
open import Graded.Usage.Restrictions 𝕄
open import Graded.Mode 𝕄

open import Tools.Bool
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.List
open import Tools.Nat as Nat using (Nat; 1+) renaming (_+_ to _+ⁿ_)
open import Tools.Product
open import Tools.Relation
open import Tools.Sum using (inj₁; inj₂)

import Tools.Reasoning.Equivalence
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality

private
  variable
    b : Bool
    α m n : Nat
    A A₁ A₂ t t₁ t₂ t₃ t₄ u : U.Term n
    v v₁ v₂ : T.Term n
    ts : DCon (U.Term _) _
    ∇ : List (T.Term n)
    σ : U.Subst m n
    σ′ : T.Subst m n
    ρ : Wk _ _
    γ : Conₘ n
    x : Fin n
    p q r : M
    k : Strength
    s : Strictness

-- Some lemmas related to how erase′ computes.

opaque

  prod-𝟘 :
    ∀ k → p PE.≡ 𝟘 →
    erase′ b s (U.prod k p t u) PE.≡ erase′ b s u
  prod-𝟘 {p} _ p≡𝟘 with is-𝟘? p
  … | yes _  = PE.refl
  … | no p≢𝟘 = ⊥-elim (p≢𝟘 p≡𝟘)

opaque

  prod-ω :
    ∀ k → p PE.≢ 𝟘 →
    erase′ b s (U.prod k p t u) PE.≡
    prod⟨ s ⟩ (erase′ b s t) (erase′ b s u)
  prod-ω {p} _ p≢𝟘 with is-𝟘? p
  … | yes p≡𝟘 = ⊥-elim (p≢𝟘 p≡𝟘)
  … | no _    = PE.refl

opaque

  fst-≢𝟘 :
    p PE.≢ 𝟘 →
    erase′ b s (U.fst p t) PE.≡ T.fst (erase′ b s t)
  fst-≢𝟘 {p} p≢𝟘 with is-𝟘? p
  … | yes p≡𝟘 = ⊥-elim (p≢𝟘 p≡𝟘)
  … | no _    = PE.refl

opaque

  snd-𝟘 :
    p PE.≡ 𝟘 →
    erase′ b s (U.snd p t) PE.≡ erase′ b s t
  snd-𝟘 {p} p≡𝟘 with is-𝟘? p
  ... | yes _  = PE.refl
  ... | no p≢𝟘 = ⊥-elim (p≢𝟘 p≡𝟘)

opaque

  snd-ω :
    p PE.≢ 𝟘 →
    erase′ b s (U.snd p t) PE.≡ T.snd (erase′ b s t)
  snd-ω {p} p≢𝟘 with is-𝟘? p
  … | yes p≡𝟘 = ⊥-elim (p≢𝟘 p≡𝟘)
  … | no _    = PE.refl

opaque

  prodrec-ω :
    ∀ q A → r PE.≢ 𝟘 →
    erase′ b s (U.prodrec r p q A t u) PE.≡
    erase-prodrecω s p (erase′ b s t) (erase′ b s u)
  prodrec-ω {r} _ _ r≢𝟘 with is-𝟘? r
  ... | yes r≡𝟘 = ⊥-elim (r≢𝟘 r≡𝟘)
  ... | no _    = PE.refl

opaque

  prodrec-𝟘 :
    ∀ q A →
    erase′ b s (U.prodrec 𝟘 p q A t u) ≡
    erase′ b s u T.[ loop s , loop s ]₁₀
  prodrec-𝟘 _ _ with is-𝟘? 𝟘
  … | yes _  = refl
  … | no 𝟘≢𝟘 = ⊥-elim (𝟘≢𝟘 refl)

opaque

  prodrec-≢𝟘-𝟘 :
    ∀ q A → r ≢ 𝟘 →
    erase′ b s (U.prodrec r 𝟘 q A t u) ≡
    T.lam (erase′ b s u T.[ T.sgSubst (loop s) T.⇑ ]) T.∘⟨ s ⟩
      erase′ b s t
  prodrec-≢𝟘-𝟘 {b} {s} {t} {u} q A r≢𝟘
    rewrite prodrec-ω {b = b} {s = s} {p = 𝟘} {t = t} {u = u} q A r≢𝟘
    with is-𝟘? 𝟘
  … | yes _  = refl
  … | no 𝟘≢𝟘 = ⊥-elim (𝟘≢𝟘 refl)

opaque

  prodrec-≢𝟘-≢𝟘 :
    ∀ q A → r ≢ 𝟘 → p ≢ 𝟘 →
    erase′ b s (U.prodrec r p q A t u) ≡
    T.prodrec (erase′ b s t) (erase′ b s u)
  prodrec-≢𝟘-≢𝟘 {p} {b} {s} {t} {u} q A r≢𝟘 p≢𝟘
    rewrite prodrec-ω {b = b} {s = s} {p = p} {t = t} {u = u} q A r≢𝟘
    with is-𝟘? p
  … | no _    = refl
  … | yes p≡𝟘 = ⊥-elim (p≢𝟘 p≡𝟘)

opaque

  unitrec-𝟘 :
    ∀ l q A → p PE.≡ 𝟘 →
    erase′ b s (U.unitrec l p q A t u) PE.≡ erase′ b s u
  unitrec-𝟘 {p} _ _ _ p≡𝟘 with is-𝟘? p
  … | yes _  = PE.refl
  … | no p≢𝟘 = ⊥-elim (p≢𝟘 p≡𝟘)

opaque

  unitrec-ω :
    ∀ l q A → p PE.≢ 𝟘 →
    erase′ b s (U.unitrec l p q A t u) PE.≡
    T.unitrec (erase′ b s t) (erase′ b s u)
  unitrec-ω {p} _ _ _ p≢𝟘 with is-𝟘? p
  … | yes p≡𝟘 = ⊥-elim (p≢𝟘 p≡𝟘)
  … | no _    = PE.refl

opaque

  ∘-≢𝟘 :
    p ≢ 𝟘 →
    erase′ b s (t U.∘⟨ p ⟩ u) ≡ erase′ b s t T.∘⟨ s ⟩ erase′ b s u
  ∘-≢𝟘 {p} p≢𝟘 with is-𝟘? p
  … | no _    = refl
  … | yes p≡𝟘 = ⊥-elim $ p≢𝟘 p≡𝟘

opaque

  ∘-𝟘 : erase′ b s (t U.∘⟨ 𝟘 ⟩ u) ≡ app-𝟘′ b s (erase′ b s t)
  ∘-𝟘 with is-𝟘? 𝟘
  … | yes _  = refl
  … | no 𝟘≢𝟘 = ⊥-elim $ 𝟘≢𝟘 refl

opaque

  lam-≢𝟘 :
    ∀ b → p ≢ 𝟘 →
    erase′ b s (U.lam p t) ≡ T.lam (erase′ b s t)
  lam-≢𝟘     false _   = refl
  lam-≢𝟘 {p} true  p≢𝟘 with is-𝟘? p
  … | no _    = refl
  … | yes p≡𝟘 = ⊥-elim $ p≢𝟘 p≡𝟘

opaque

  lam-𝟘-keep :
    (t : U.Term (1+ n)) →
    erase′ false s (U.lam 𝟘 t) ≡ T.lam (erase′ false s t)
  lam-𝟘-keep _ with is-𝟘? 𝟘
  … | yes _  = refl
  … | no 𝟘≢𝟘 = ⊥-elim $ 𝟘≢𝟘 refl

opaque

  lam-𝟘-remove :
    erase′ true s (U.lam 𝟘 t) ≡ erase′ true s t T.[ loop s ]₀
  lam-𝟘-remove with is-𝟘? 𝟘
  … | yes _  = refl
  … | no 𝟘≢𝟘 = ⊥-elim $ 𝟘≢𝟘 refl

opaque
  unfolding subst

  erase-subst :
    erase′ b s (subst p A₁ A₂ t₁ t₂ t₃ t₄) PE.≡ erase′ b s t₄
  erase-subst = PE.refl

opaque
  unfolding substᵉ subst

  erase-substᵉ :
    erase′ b s (substᵉ k A₁ A₂ t₁ t₂ t₃ t₄) PE.≡ erase′ b s t₄
  erase-substᵉ = PE.refl

opaque
  unfolding Jᵉ substᵉ subst

  erase-Jᵉ : erase′ b s (Jᵉ k A₁ t₁ A₂ t₂ t₃ t₄) PE.≡ erase′ b s t₂
  erase-Jᵉ = PE.refl

opaque

  -- The result of weakening loop? s is loop? s.

  wk-loop? : ∀ s → wk ρ (loop? s) ≡ loop? s
  wk-loop? non-strict = wk-loop
  wk-loop? strict     = refl

opaque

  -- The result of applying a substitution to loop? s is loop? s.

  loop?-[] : ∀ s → loop? s T.[ σ′ ] ≡ loop? s
  loop?-[] non-strict = loop-[]
  loop?-[] strict     = refl

opaque

  -- The term loop? s is closed.

  loop?-closed : ∀ s → ¬ HasX x (loop? s)
  loop?-closed non-strict = loop-closed
  loop?-closed strict     = λ ()

opaque

  -- The term loop? {n = n} s satisfies Value⟨ s ⟩.

  Value⟨⟩-loop? : ∀ s → Value⟨ s ⟩ (loop? {n = n} s)
  Value⟨⟩-loop? non-strict = _
  Value⟨⟩-loop? strict     = T.↯

opaque

  -- A reduction lemma for app-𝟘′.

  app-𝟘′-subst : ∇ T.⊢ v₁ ⇒ v₂ → ∇ T.⊢ app-𝟘′ b s v₁ ⇒ app-𝟘′ b s v₂
  app-𝟘′-subst {b = true}  v₁⇒v₂ = v₁⇒v₂
  app-𝟘′-subst {b = false} v₁⇒v₂ = app-subst v₁⇒v₂

-- The functions wk ρ/U.wk ρ and erase′ b s commute.

wk-erase-comm : (ρ : U.Wk m n) (t : U.Term n)
              → wk ρ (erase′ b s t) ≡ erase′ b s (U.wk ρ t)
wk-erase-comm _ (var _) = refl
wk-erase-comm _ (defn _) = refl
wk-erase-comm {s} _ (U _) = wk-loop? s
wk-erase-comm {s} _ (ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _) = wk-loop? s
wk-erase-comm {b = true} {s} ρ (U.lam p t) with is-𝟘? p
... | no _  = cong T.lam $ wk-erase-comm _ t
... | yes _ =
  wk ρ (erase′ true s t T.[ loop s ]₀)                ≡⟨ wk-β (erase′ _ _ t) ⟩
  wk (lift ρ) (erase′ true s t) T.[ wk ρ (loop s) ]₀  ≡⟨ cong (wk _ (erase′ _ _ t) T.[_]₀) wk-loop ⟩
  wk (lift ρ) (erase′ true s t) T.[ loop s ]₀         ≡⟨ cong T._[ _ ]₀ $ wk-erase-comm _ t ⟩
  erase′ true s (U.wk (lift ρ) t) T.[ loop s ]₀       ∎
  where
  open Tools.Reasoning.PropositionalEquality
wk-erase-comm {b = false} ρ (U.lam p t) =
  cong T.lam (wk-erase-comm (lift ρ) t)
wk-erase-comm ρ (t U.∘⟨ p ⟩ u) with is-𝟘? p
wk-erase-comm {b = false} {s} _ (t U.∘⟨ _ ⟩ _) | yes _ =
  cong₂ T._∘⟨ _ ⟩_ (wk-erase-comm _ t) (wk-loop? s)
wk-erase-comm {b = true} _ (t U.∘⟨ _ ⟩ _) | yes _ =
  wk-erase-comm _ t
wk-erase-comm _ (t U.∘⟨ _ ⟩ u) | no _ =
  cong₂ T._∘⟨ _ ⟩_ (wk-erase-comm _ t) (wk-erase-comm _ u)
wk-erase-comm {b} {s} ρ (U.prod _ p t u) with is-𝟘? p
... | yes _ = wk-erase-comm ρ u
... | no _ =
  wk ρ (prod⟨ s ⟩ (erase′ b s t) (erase′ b s u))             ≡⟨ wk-prod⟨⟩ ⟩
  prod⟨ s ⟩ (wk ρ (erase′ b s t)) (wk ρ (erase′ b s u))      ≡⟨ cong₂ prod⟨ _ ⟩ (wk-erase-comm _ t) (wk-erase-comm _ u) ⟩
  prod⟨ s ⟩ (erase′ b s (U.wk ρ t)) (erase′ b s (U.wk ρ u))  ∎
  where
  open Tools.Reasoning.PropositionalEquality
wk-erase-comm ρ (U.fst p t) with is-𝟘? p
... | yes _ = wk-loop
... | no _ = cong T.fst (wk-erase-comm ρ t)
wk-erase-comm ρ (U.snd p t) with is-𝟘? p
... | yes _ = wk-erase-comm ρ t
... | no _ = cong T.snd (wk-erase-comm ρ t)
wk-erase-comm {b} {s} ρ (U.prodrec r p _ A t u) with is-𝟘? r
... | yes _ =
  wk ρ (erase′ b s u [ loop s , loop s ]₁₀)                              ≡⟨ wk-β-doubleSubst _ (erase′ _ _ u) _ _ ⟩
  wk (lift (lift ρ)) (erase′ b s u) [ wk ρ (loop s) , wk ρ (loop s) ]₁₀  ≡⟨ cong₃ _[_,_]₁₀ (wk-erase-comm _ u) wk-loop wk-loop ⟩
  erase′ b s (U.wk (lift (lift ρ)) u) [ loop s , loop s ]₁₀              ∎
  where
  open Tools.Reasoning.PropositionalEquality
... | no _ with is-𝟘? p
... | yes _ =
  T.lam (wk (lift ρ) (erase′ b s u T.[ liftSubst (T.sgSubst (loop s)) ]))
    T.∘⟨ s ⟩ wk ρ (erase′ b s t)                                           ≡⟨ cong (λ u → T.lam u T.∘⟨ _ ⟩ _) $
                                                                              wk-lift-β (erase′ _ _ u) ⟩
  T.lam (wk (lift (lift ρ)) (erase′ b s u)
           T.[ liftSubst (T.sgSubst (wk ρ (loop s))) ])
    T.∘⟨ s ⟩ wk ρ (erase′ b s t)                                           ≡⟨ cong₃ (λ u v t → T.lam (u T.[ T.liftSubst (T.sgSubst v) ]) T.∘⟨ _ ⟩ t)
                                                                                (wk-erase-comm _ u)
                                                                                wk-loop
                                                                                (wk-erase-comm _ t) ⟩
  T.lam (erase′ b s (U.wk (lift (lift ρ)) u)
           T.[ liftSubst (T.sgSubst (loop s)) ])
    T.∘⟨ s ⟩ erase′ b s (U.wk ρ t)                                         ∎
  where
  open Tools.Reasoning.PropositionalEquality
... | no _ = cong₂ T.prodrec (wk-erase-comm ρ t)
                   (wk-erase-comm (lift (lift ρ)) u)
wk-erase-comm {s} _ ℕ = wk-loop? s
wk-erase-comm ρ U.zero = refl
wk-erase-comm {b} {s} ρ (U.suc t) =
  wk ρ (suc⟨ s ⟩ (erase′ b s t))    ≡⟨ wk-suc⟨⟩ ⟩
  suc⟨ s ⟩ (wk ρ (erase′ b s t))    ≡⟨ cong suc⟨ _ ⟩ (wk-erase-comm _ t) ⟩
  suc⟨ s ⟩ (erase′ b s (U.wk ρ t))  ∎
  where
  open Tools.Reasoning.PropositionalEquality
wk-erase-comm ρ (U.natrec p q r A z s n) =
  cong₃ T.natrec (wk-erase-comm ρ z)
                 (wk-erase-comm (lift (lift ρ)) s)
                 (wk-erase-comm ρ n)
wk-erase-comm {s} _ Unit! = wk-loop? s
wk-erase-comm ρ U.star! = refl
wk-erase-comm ρ (U.unitrec _ p _ _ t u)
  with is-𝟘? p
... | yes _ =
  wk-erase-comm _ u
... | no _ =
  cong₂ T.unitrec (wk-erase-comm ρ t)
                  (wk-erase-comm ρ u)
wk-erase-comm {s} _ Empty = wk-loop? s
wk-erase-comm _ (emptyrec _ _ _) = wk-loop
wk-erase-comm {s} _ (Id _ _ _) = wk-loop? s
wk-erase-comm {s} _ U.rfl = wk-loop? s
wk-erase-comm _ (J _ _ _ _ _ u _ _) = wk-erase-comm _ u
wk-erase-comm _ (K _ _ _ _ u _) = wk-erase-comm _ u
wk-erase-comm {s} _ ([]-cong _ _ _ _ _) = wk-loop? s

-- Lifting substitutions commute with erase

liftSubst-erase-comm :
  (x : Fin (1+ n)) →
  liftSubst (eraseSubst′ b s σ) x ≡ eraseSubst′ b s (U.liftSubst σ) x
liftSubst-erase-comm     x0     = refl
liftSubst-erase-comm {σ} (_ +1) = wk-erase-comm _ (σ _)

-- Multiple lifts commutes with erase

liftSubsts-erase-comm :
  (k : Nat) (x : Fin (k +ⁿ n)) →
  T.liftSubstn (eraseSubst′ b s σ) k x ≡
  eraseSubst′ b s (U.liftSubstn σ k) x
liftSubsts-erase-comm 0 x = refl
liftSubsts-erase-comm (1+ k) x0 = refl
liftSubsts-erase-comm {b} {s} {σ} (1+ k) (x +1) =
  T.wk1 (T.liftSubstn (eraseSubst′ b s σ) k x)          ≡⟨ cong T.wk1 $ liftSubsts-erase-comm k _ ⟩
  T.wk1 (eraseSubst′ b s (U.liftSubstn σ k) x)          ≡⟨⟩
  wk (step id) (eraseSubst′ b s (U.liftSubstn σ k) x)   ≡⟨ wk-erase-comm _ (U.liftSubstn σ _ _) ⟩
  erase′ b s (U.wk (U.step U.id) (U.liftSubstn σ k x))  ≡⟨⟩
  eraseSubst′ b s (U.liftSubstn σ (1+ k)) (x +1)        ∎
  where
  open Tools.Reasoning.PropositionalEquality

opaque

  -- A substitution lemma for app-𝟘′.

  app-𝟘-[] :
    (t : T.Term n) →
    app-𝟘′ b s t T.[ σ′ ] ≡
    app-𝟘′ b s (t T.[ σ′ ])
  app-𝟘-[] {b = true}      _ = refl
  app-𝟘-[] {b = false} {s} _ = cong (T._∘⟨_⟩_ _ _) $ loop?-[] s

-- Substitution commutes with erase′ b s (modulo the translation of
-- the substitution to the target language).

subst-erase-comm :
  (σ : U.Subst m n) (t : U.Term n) →
  erase′ b s t T.[ eraseSubst′ b s σ ] ≡ erase′ b s (t U.[ σ ])
subst-erase-comm σ (var x) = refl
subst-erase-comm _ (defn _) = refl
subst-erase-comm {s} _ (U _) = loop?-[] s
subst-erase-comm {s} _ (ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _) = loop?-[] s
subst-erase-comm {b = true} {s} σ (U.lam p t) with is-𝟘? p
... | no _ =
  cong T.lam
    (erase′ true s t T.[ liftSubst (eraseSubst′ true s σ) ]    ≡⟨ substVar-to-subst liftSubst-erase-comm (erase′ _ _ t) ⟩
     erase′ true s t T.[ eraseSubst′ true s (U.liftSubst σ) ]  ≡⟨ subst-erase-comm _ t ⟩
     erase′ true s (t U.[ U.liftSubst σ ])                     ∎)
  where
  open Tools.Reasoning.PropositionalEquality
... | yes _ =
  erase′ true s t T.[ loop s ]₀ T.[ (eraseSubst′ true s σ) ]            ≡⟨ singleSubstLift (erase′ _ _ t) _ ⟩

  erase′ true s t T.[ liftSubst (eraseSubst′ true s σ) ]
    T.[ loop s [ eraseSubst′ true s σ ] ]₀                              ≡⟨ cong (erase′ _ _ t T.[ liftSubst _ ] T.[_]₀) loop-[] ⟩

  erase′ true s t T.[ liftSubst (eraseSubst′ true s σ) ] T.[ loop s ]₀  ≡⟨ cong T._[ _ ]₀ $ substVar-to-subst liftSubst-erase-comm (erase′ _ _ t) ⟩

  erase′ true s t T.[ eraseSubst′ true s (U.liftSubst σ) ]
    T.[ loop s ]₀                                                       ≡⟨ cong T._[ _ ]₀ $ subst-erase-comm _ t ⟩

  erase′ true s (t U.[ U.liftSubst σ ]) T.[ loop s ]₀                   ∎
  where
  open Tools.Reasoning.PropositionalEquality
subst-erase-comm {b = false} {s} σ (U.lam _ t) =
  cong Term.lam
    (erase′ false s t T.[ liftSubst (eraseSubst′ false s σ) ]    ≡⟨ substVar-to-subst (liftSubsts-erase-comm 1) (erase′ _ _ t) ⟩
     erase′ false s t T.[ eraseSubst′ false s (U.liftSubst σ) ]  ≡⟨ subst-erase-comm _ t ⟩
     erase′ false s (t U.[ U.liftSubst σ ])                      ∎)
  where
  open Tools.Reasoning.PropositionalEquality
subst-erase-comm σ (t U.∘⟨ p ⟩ u) with is-𝟘? p
subst-erase-comm {b} {s} σ (t U.∘⟨ _ ⟩ _) | yes _ =
  app-𝟘′ b s (erase′ b s t) T.[ eraseSubst′ b s σ ]  ≡⟨ app-𝟘-[] (erase′ _ _ t) ⟩
  app-𝟘′ b s (erase′ b s t T.[ eraseSubst′ b s σ ])  ≡⟨ cong (app-𝟘′ _ _) $ subst-erase-comm _ t ⟩
  app-𝟘′ b s (erase′ b s (t U.[ σ ]))                ∎
  where
  open Tools.Reasoning.PropositionalEquality
subst-erase-comm σ (t U.∘⟨ _ ⟩ u) | no _ =
  cong₂ T._∘⟨ _ ⟩_ (subst-erase-comm σ t) (subst-erase-comm σ u)
subst-erase-comm {b} {s} σ (U.prod _ p t u) with is-𝟘? p
... | yes _ = subst-erase-comm σ u
... | no _ =
  prod⟨ s ⟩ (erase′ b s t) (erase′ b s u) [ eraseSubst′ b s σ ]  ≡⟨ prod⟨⟩-[] ⟩

  prod⟨ s ⟩ (erase′ b s t [ eraseSubst′ b s σ ])
    (erase′ b s u [ eraseSubst′ b s σ ])                         ≡⟨ cong₂ prod⟨ _ ⟩ (subst-erase-comm _ t) (subst-erase-comm _ u) ⟩

  prod⟨ s ⟩ (erase′ b s (t U.[ σ ])) (erase′ b s (u U.[ σ ]))    ∎
  where
  open Tools.Reasoning.PropositionalEquality
subst-erase-comm σ (U.fst p t) with is-𝟘? p
... | yes _ = loop-[]
... | no _ = cong T.fst (subst-erase-comm σ t)
subst-erase-comm σ (U.snd p t) with is-𝟘? p
... | yes _ = subst-erase-comm σ t
... | no _  = cong T.snd (subst-erase-comm σ t)
subst-erase-comm {b} {s} σ (U.prodrec r p _ A t u) with is-𝟘? r
... | yes _ =
  erase′ b s u [ loop s , loop s ]₁₀ T.[ eraseSubst′ b s σ ]   ≡⟨ doubleSubstLift _ (erase′ _ _ u) _ _ ⟩

  erase′ b s u T.[ T.liftSubstn (eraseSubst′ b s σ) 2 ]
    [ loop s T.[ eraseSubst′ b s σ ]
    , loop s T.[ eraseSubst′ b s σ ]
    ]₁₀                                                        ≡⟨ cong₃ _[_,_]₁₀
                                                                    (substVar-to-subst (liftSubsts-erase-comm 2) (erase′ _ _ u))
                                                                    loop-[]
                                                                    loop-[] ⟩
  erase′ b s u T.[ eraseSubst′ b s (U.liftSubstn σ 2) ]
    [ loop s , loop s ]₁₀                                      ≡⟨ cong _[ _ , _ ]₁₀ $
                                                                  subst-erase-comm _ u ⟩
  erase′ b s (u U.[ U.liftSubstn σ 2 ]) [ loop s , loop s ]₁₀  ∎
  where
  open Tools.Reasoning.PropositionalEquality
... | no _ with is-𝟘? p
... | yes _ =
  T.lam (erase′ b s u T.[ liftSubst (T.sgSubst (loop s)) ]
           T.[ liftSubst (eraseSubst′ b s σ) ])
    T.∘⟨ s ⟩ (erase′ b s t T.[ eraseSubst′ b s σ ])                       ≡⟨ cong (λ u → T.lam u T.∘⟨ _ ⟩ _) $
                                                                             subst-liftSubst-sgSubst (erase′ _ _ u) ⟩
  T.lam (erase′ b s u T.[ T.liftSubstn (eraseSubst′ b s σ) 2 ]
           T.[ liftSubst (T.sgSubst (loop s T.[ eraseSubst′ b s σ ])) ])
    T.∘⟨ s ⟩ (erase′ b s t T.[ eraseSubst′ b s σ ])                       ≡⟨ cong (λ u → T.lam (u T.[ _ ]) T.∘⟨ _ ⟩ _) $
                                                                             substVar-to-subst (liftSubsts-erase-comm 2) (erase′ _ _ u) ⟩
  T.lam (erase′ b s u T.[ eraseSubst′ b s (U.liftSubstn σ 2) ]
           T.[ liftSubst (T.sgSubst (loop s T.[ eraseSubst′ b s σ ])) ])
    T.∘⟨ s ⟩ (erase′ b s t T.[ eraseSubst′ b s σ ])                       ≡⟨ cong₃ (λ u v t → T.lam (u T.[ liftSubst (T.sgSubst v) ]) T.∘⟨ _ ⟩ t)
                                                                               (subst-erase-comm _ u)
                                                                               loop-[]
                                                                               (subst-erase-comm _ t) ⟩
  T.lam (erase′ b s (u U.[ U.liftSubstn σ 2 ])
           T.[ liftSubst (T.sgSubst (loop s)) ])
    T.∘⟨ s ⟩ erase′ b s (t U.[ σ ])                                       ∎
  where
  open Tools.Reasoning.PropositionalEquality
... | no _ =
  cong₂ Term.prodrec (subst-erase-comm σ t)
    (trans (substVar-to-subst (liftSubsts-erase-comm 2) (erase′ _ _ u))
       (subst-erase-comm (U.liftSubstn σ 2) u))
subst-erase-comm {s} _ ℕ = loop?-[] s
subst-erase-comm σ U.zero = refl
subst-erase-comm {b} {s} σ (U.suc t) =
  suc⟨ s ⟩ (erase′ b s t) T.[ eraseSubst′ b s σ ]  ≡⟨ suc⟨⟩-[] ⟩
  suc⟨ s ⟩ (erase′ b s t T.[ eraseSubst′ b s σ ])  ≡⟨ cong suc⟨ _ ⟩ (subst-erase-comm _ t) ⟩
  suc⟨ s ⟩ (erase′ b s (t U.[ σ ]))                ∎
  where
  open Tools.Reasoning.PropositionalEquality
subst-erase-comm σ (U.natrec p q r A z s n) = cong₃ T.natrec
  (subst-erase-comm σ z)
  (trans (substVar-to-subst (liftSubsts-erase-comm 2) (erase′ _ _ s))
         (subst-erase-comm (U.liftSubst (U.liftSubst σ)) s))
  (subst-erase-comm σ n)
subst-erase-comm {s} _ Unit! = loop?-[] s
subst-erase-comm σ U.star! = refl
subst-erase-comm σ (U.unitrec _ p _ _ t u) with is-𝟘? p
... | yes _ =
  subst-erase-comm σ u
... | no _ =
  cong₂ T.unitrec (subst-erase-comm σ t)
                  (subst-erase-comm σ u)
subst-erase-comm {s} _ Empty = loop?-[] s
subst-erase-comm _ (emptyrec _ _ _) = loop-[]
subst-erase-comm {s} _ (Id _ _ _) = loop?-[] s
subst-erase-comm {s} _ U.rfl = loop?-[] s
subst-erase-comm _ (J _ _ _ _ _ u _ _) = subst-erase-comm _ u
subst-erase-comm _ (K _ _ _ _ u _) = subst-erase-comm _ u
subst-erase-comm {s} _ ([]-cong _ _ _ _ _) = loop?-[] s

subst-undefined : (x : Fin (1+ n)) →
      eraseSubst′ b s (U.sgSubst Empty) x ≡
      T.sgSubst (loop? s) x
subst-undefined x0 = refl
subst-undefined (x +1) = refl

erase-consSubst-var : (σ : U.Subst m n) (a : U.Term m) (x : Fin (1+ n))
                    → T.consSubst (eraseSubst′ b s σ) (erase′ b s a) x
                    ≡ eraseSubst′ b s (U.consSubst σ a) x
erase-consSubst-var σ a x0 = refl
erase-consSubst-var σ a (x +1) = refl

erase-consSubst : (σ : U.Subst m n) (a : U.Term m) (t : T.Term (1+ n))
                → t T.[ T.consSubst (eraseSubst′ b s σ) (erase′ b s a) ]
                ≡ t T.[ eraseSubst′ b s (U.consSubst σ a) ]
erase-consSubst σ a t = substVar-to-subst (erase-consSubst-var σ a) t

opaque
  unfolding eraseDCon′

  -- Glassification does not affect the result of eraseDCon′.

  eraseDCon-glassify :
    {∇ : DCon (U.Term 0) n} →
    eraseDCon′ b s (glassify ∇) ≡ eraseDCon′ b s ∇
  eraseDCon-glassify {∇ = ε}                 = refl
  eraseDCon-glassify {∇ = ∇ ∙⟨ _ ⟩[ _ ∷ _ ]} =
    cong (_++ _) (eraseDCon-glassify {∇ = ∇})

opaque
  unfolding eraseDCon′

  -- The length of eraseDCon′ b s ts is the length of ts.

  length-eraseDCon :
    (ts : DCon (U.Term 0) n) → length (eraseDCon′ b s ts) ≡ n
  length-eraseDCon         ε                         = refl
  length-eraseDCon {b} {s} (_∙⟨_⟩[_∷_] {n} ts _ t _) =
    length (eraseDCon′ b s ts ++ erase′ b s t ∷ [])  ≡⟨ length-++ (eraseDCon′ _ _ ts) ⟩
    length (eraseDCon′ b s ts) +ⁿ 1                  ≡˘⟨ Nat.+-comm 1 _ ⟩
    1+ (length (eraseDCon′ b s ts))                  ≡⟨ cong 1+ (length-eraseDCon ts) ⟩
    1+ n                                             ∎
    where
    open Tools.Reasoning.PropositionalEquality

opaque
  unfolding eraseDCon′

  -- If α points to t in ts, then α points to erase′ b s t in
  -- eraseDCon′ b s ts.

  ↦erase∈eraseDCon :
    α U.↦ t ∷ A ∈ ts → α ↦ erase′ b s t ∈ eraseDCon′ b s ts
  ↦erase∈eraseDCon (there α↦t) = ↦∈++ (↦erase∈eraseDCon α↦t)
  ↦erase∈eraseDCon (here {∇})  =
    PE.subst₃ _↦_∈_ (length-eraseDCon ∇) refl refl length↦∈++∷

opaque

  -- If α points to t in glassify ts, then α points to erase′ b s t in
  -- eraseDCon′ b s ts.

  ↦erase∈eraseDCon′ :
    α U.↦ t ∷ A ∈ glassify ts → α ↦ erase′ b s t ∈ eraseDCon′ b s ts
  ↦erase∈eraseDCon′ =
    PE.subst (_↦_∈_ _ _) eraseDCon-glassify ∘→
    ↦erase∈eraseDCon

opaque
  unfolding Ω O.ω loop

  -- The term erase′ b s (Ω {n = n} p) does not reduce to a value.
  --
  -- Note that erase′ true s (Ω {n = n} 𝟘) could have been a value if
  -- erasure had been defined differently for lambdas with erased
  -- arguments in the "b = true" case: this term is (at the time of
  -- writing) equal to loop s due to the use of loop s in
  -- erase″ t T.[ loop s ]₀, but if this right-hand side had instead
  -- been erase″ t T.[ zero ]₀, then the term would have been equal to
  -- zero.

  erase-Ω-does-not-have-a-value :
    Value v → ¬ ∇ ⊢ erase′ b s (Ω {n = n} p) ⇒* v
  erase-Ω-does-not-have-a-value {v} {∇} {b} {s} {p} v-value
    with is-𝟘? p
  … | no p≢𝟘 =
    PE.subst (λ t → ¬ ∇ ⊢ t ∘⟨ s ⟩ t ⇒* v) (PE.sym $ lam-≢𝟘 b p≢𝟘) $
    PE.subst (λ t → ¬ ∇ ⊢ lam t ∘⟨ s ⟩ lam t ⇒* v) (PE.sym $ ∘-≢𝟘 p≢𝟘) $
    ¬loop⇒* v-value
  erase-Ω-does-not-have-a-value {v} {∇} {b = true} {s} {p} v-value
    | yes refl =
    PE.subst (λ t → ¬ ∇ ⊢ t ⇒* v) (PE.sym lam-𝟘-remove) $
    PE.subst (λ t → ¬ ∇ ⊢ t T.[ loop s ]₀ ⇒* v) (PE.sym ∘-𝟘) $
    ¬loop⇒* v-value
  erase-Ω-does-not-have-a-value {v} {∇} {b = false} {s} {p} v-value
    | yes refl =
    PE.subst (λ t → ¬ ∇ ⊢ lam t ∘⟨ s ⟩ loop? s ⇒* v) (PE.sym ∘-𝟘)
      (lemma _)
    where
    lemma : ∀ s → ¬ ∇ ⊢ lam (var x0 ∘⟨ s ⟩ loop? s) ∘⟨ s ⟩ loop? s ⇒* v
    lemma strict T.refl =
      case v-value of λ ()
    lemma strict (T.trans (app-subst ()) _)
    lemma strict (T.trans (app-subst-arg _ ()) _)
    lemma strict (T.trans (β-red _) T.refl) =
      case v-value of λ ()
    lemma strict (T.trans (β-red _) (T.trans (app-subst ()) _))
    lemma strict (T.trans (β-red _) (T.trans (app-subst-arg _ ()) _))
    lemma non-strict T.refl =
      case v-value of λ ()
    lemma non-strict (T.trans (app-subst ()) _)
    lemma non-strict (T.trans (β-red _) loop∘loop⇒v) =
      let _ , v′-value , loop⇒v′ = ∘⇒Value→⇒Value v-value loop∘loop⇒v in
      ¬loop⇒* v′-value loop⇒v′

module hasX (R : Usage-restrictions) where

  open MU R
  open MUP R
  open MUP𝟘 R

  open import Graded.Usage.Restrictions.Instance R

  private opaque

    -- A lemma used in the proof of erase-≔.

    erase-≔-var :
      ⦃ 𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet ⦄ →
      ∀ (x y : Fin (1+ n)) {u} → x ◂ 𝟘 ∈ (𝟘ᶜ , y ≔ 𝟙) →
      wk (step-at x) (erase′ b s (⟨ x ≔ u ⟩ y)) ≡ var y
    erase-≔-var x0 x0 erased =
      ⊥-elim $ non-trivial $ sym $ x0◂∈ erased
    erase-≔-var x0 (_ +1) _ =
      refl
    erase-≔-var (_+1 {n = 0} ())
    erase-≔-var (_+1 {n = 1+ _} _) x0 _ =
      refl
    erase-≔-var {b} {s} (_+1 {n = 1+ _} x) (y +1) {u} erased =
      wk (lift (step-at x)) (erase′ b s (U.wk1 (⟨ x ≔ u ⟩ y)))  ≡˘⟨ cong (wk _) $ wk-erase-comm _ (⟨ x ≔ _ ⟩ _) ⟩
      wk (lift (step-at x)) (T.wk1 (erase′ b s (⟨ x ≔ u ⟩ y)))  ≡˘⟨ wk1-wk≡lift-wk1 _ _ ⟩
      T.wk1 (wk (step-at x) (erase′ b s (⟨ x ≔ u ⟩ y)))         ≡⟨ cong T.wk1 $ erase-≔-var x y (+1◂∈ erased) ⟩
      var (y +1)                                                ∎
      where
      open Tools.Reasoning.PropositionalEquality

  opaque

    -- Substituting something for an erasable variable does not affect
    -- the result of erasure (if we ignore shifting of free
    -- variables).

    erase-≔ :
      ∀ {x : Fin n} {u}
      ⦃ 𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet ⦄ →
      x ◂ 𝟘 ∈ γ → γ ▸[ 𝟙ᵐ ] t →
      wk (step-at x) (erase′ b s (t U.[ ⟨ x ≔ u ⟩ ])) ≡ erase′ b s t
    erase-≔ {n = 0} {x = ()}
    erase-≔ erased (sub ▸t γ≤δ) =
      erase-≔ (x◂𝟘∈γ≤δ erased γ≤δ) ▸t
    erase-≔ {n = 1+ _} erased var =
      erase-≔-var _ _ erased
    erase-≔ _ defn =
      refl
    erase-≔ {s} _ Uₘ =
      wk-loop? s
    erase-≔ {s} _ Emptyₘ =
      wk-loop? s
    erase-≔ _ (emptyrecₘ _ _ _) =
      wk-loop
    erase-≔ {s} _ Unitₘ =
      wk-loop? s
    erase-≔ _ (starˢₘ _) =
      refl
    erase-≔ _ starʷₘ =
      refl
    erase-≔ erased (unitrecₘ {p} ▸t₁ ▸t₂ _ _) with is-𝟘? p
    … | no p≢𝟘 =
      cong₂ unitrec
        (erase-≔ (x◂𝟘∈pγ refl p≢𝟘 (x◂𝟘∈γ+δˡ refl erased))
           (▸-cong (≢𝟘→⌞⌟≡𝟙ᵐ p≢𝟘) ▸t₁))
        (erase-≔ (x◂𝟘∈γ+δʳ refl erased) ▸t₂)
    … | yes _ =
      erase-≔ (x◂𝟘∈γ+δʳ refl erased) ▸t₂
    erase-≔ {s} _ (ΠΣₘ _ _) =
      wk-loop? s
    erase-≔ {n = 1+ _} {b = false} erased (lamₘ ▸t) =
      cong lam (erase-≔ (there erased) ▸t)
    erase-≔ {n = 1+ _} {b = true} {s} {x} {u} erased (lamₘ {p} {t} ▸t)
      with is-𝟘? p
    … | no _ =
      cong lam (erase-≔ (there erased) ▸t)
    … | yes _ =
      wk (step-at x)
        (erase′ true s (t U.[ ⟨ x ≔ u ⟩ U.⇑ ]) T.[ loop s ]₀)        ≡⟨ wk-β (erase′ _ _ (t U.[ _ ])) ⟩

      wk (lift (step-at x)) (erase′ true s (t U.[ ⟨ x ≔ u ⟩ U.⇑ ]))
        T.[ wk (step-at x) (loop s) ]₀                               ≡⟨ cong (wk _ (erase′ _ _ (t U.[ _ ])) T.[_]₀) wk-loop ⟩

      wk (lift (step-at x)) (erase′ true s (t U.[ ⟨ x ≔ u ⟩ U.⇑ ]))
        T.[ loop s ]₀                                                ≡⟨ cong T._[ _ ]₀ $ erase-≔ (there erased) ▸t ⟩

      erase′ true s t T.[ loop s ]₀                                  ∎
      where
      open Tools.Reasoning.PropositionalEquality
    erase-≔ erased (_∘ₘ_ {p} ▸t ▸u) with is-𝟘? p
    … | no p≢𝟘 =
      cong₂ _∘⟨ _ ⟩_ (erase-≔ (x◂𝟘∈γ+δˡ refl erased) ▸t)
        (erase-≔ (x◂𝟘∈pγ refl p≢𝟘 (x◂𝟘∈γ+δʳ refl erased))
           (▸-cong (≢𝟘→⌞⌟≡𝟙ᵐ p≢𝟘) ▸u))
    erase-≔ {b = false} {s} erased (▸t ∘ₘ _) | yes _ =
      cong₂ _∘⟨ _ ⟩_ (erase-≔ (x◂𝟘∈γ+δˡ refl erased) ▸t)
        (wk-loop? s)
    erase-≔ {b = true} erased (▸t ∘ₘ _) | yes _ =
      erase-≔ (x◂𝟘∈γ+δˡ refl erased) ▸t
    erase-≔
      {b} {s} {x} {u} erased (prodˢₘ {p} {t = t₁} {u = t₂} ▸t₁ ▸t₂)
      with is-𝟘? p
    … | yes _ =
      erase-≔ (x◂𝟘∈γ∧δʳ refl erased) ▸t₂
    … | no p≢𝟘 =
      wk (step-at x)
        (prod⟨ s ⟩ (erase′ b s (t₁ U.[ ⟨ x ≔ u ⟩ ]))
           (erase′ b s (t₂ U.[ ⟨ x ≔ u ⟩ ])))                       ≡⟨ wk-prod⟨⟩ ⟩

      prod⟨ s ⟩ (wk (step-at x) (erase′ b s (t₁ U.[ ⟨ x ≔ u ⟩ ])))
        (wk (step-at x) (erase′ b s (t₂ U.[ ⟨ x ≔ u ⟩ ])))          ≡⟨ cong₂ prod⟨ _ ⟩
                                                                         (erase-≔ (x◂𝟘∈pγ refl p≢𝟘 (x◂𝟘∈γ∧δˡ refl erased))
                                                                            (▸-cong (≢𝟘→⌞⌟≡𝟙ᵐ p≢𝟘) ▸t₁))
                                                                         (erase-≔ (x◂𝟘∈γ∧δʳ refl erased) ▸t₂) ⟩
      prod⟨ s ⟩ (erase′ b s t₁) (erase′ b s t₂)                     ∎
      where
      open Tools.Reasoning.PropositionalEquality
    erase-≔ erased (fstₘ {p} _ ▸t eq _) with is-𝟘? p
    … | yes _ =
      wk-loop
    … | no _ =
      cong fst (erase-≔ erased (▸-cong eq ▸t))
    erase-≔ erased (sndₘ {p} ▸t) with is-𝟘? p
    … | yes _ =
      erase-≔ erased ▸t
    … | no _ =
      cong snd (erase-≔ erased ▸t)
    erase-≔
      {b} {s} {x} {u} erased (prodʷₘ {p} {t = t₁} {u = t₂} ▸t₁ ▸t₂)
      with is-𝟘? p
    … | yes _ =
      erase-≔ (x◂𝟘∈γ+δʳ refl erased) ▸t₂
    … | no p≢𝟘 =
      wk (step-at x)
        (prod⟨ s ⟩ (erase′ b s (t₁ U.[ ⟨ x ≔ u ⟩ ]))
           (erase′ b s (t₂ U.[ ⟨ x ≔ u ⟩ ])))                       ≡⟨ wk-prod⟨⟩ ⟩

      prod⟨ s ⟩ (wk (step-at x) (erase′ b s (t₁ U.[ ⟨ x ≔ u ⟩ ])))
        (wk (step-at x) (erase′ b s (t₂ U.[ ⟨ x ≔ u ⟩ ])))          ≡⟨ cong₂ prod⟨ _ ⟩
                                                                         (erase-≔ (x◂𝟘∈pγ refl p≢𝟘 (x◂𝟘∈γ+δˡ refl erased))
                                                                            (▸-cong (≢𝟘→⌞⌟≡𝟙ᵐ p≢𝟘) ▸t₁))
                                                                         (erase-≔ (x◂𝟘∈γ+δʳ refl erased) ▸t₂) ⟩
      prod⟨ s ⟩ (erase′ b s t₁) (erase′ b s t₂)                     ∎
      where
      open Tools.Reasoning.PropositionalEquality
    erase-≔
      {n = 1+ _} {b} {s} {x} {u}
      erased (prodrecₘ {r} {p} {u = t₂} ▸t₁ ▸t₂ _ _)
      with is-𝟘? r
    … | yes _ =
      wk (step-at x)
        (erase′ b s (t₂ U.[ ⟨ x +2 ≔ u ⟩ ]) [ loop s , loop s ]₁₀)  ≡⟨ wk-β-doubleSubst _ (erase′ _ _ (t₂ U.[ _ ])) _ _ ⟩

      wk (step-at (x +2)) (erase′ b s (t₂ U.[ ⟨ x +2 ≔ u ⟩ ]))
        [ wk (step-at x) (loop s) , wk (step-at x) (loop s) ]₁₀     ≡⟨ cong₃ _[_,_]₁₀ (erase-≔ (there (there (x◂𝟘∈γ+δʳ refl erased))) ▸t₂)
                                                                         wk-loop wk-loop ⟩
      erase′ b s t₂ [ loop s , loop s ]₁₀                           ∎
      where
      open Tools.Reasoning.PropositionalEquality
    … | no r≢𝟘 with is-𝟘? p
    …   | yes _ =
        cong₃ _∘⟨_⟩_
          (cong lam
             (wk (step-at (x +1))
                (erase′ b s (t₂ U.[ ⟨ x +2 ≔ u ⟩ ])
                   [ T.sgSubst (loop s) T.⇑ ])                           ≡⟨ wk-lift-β (erase′ _ _ (t₂ U.[ _ ])) ⟩

              wk (step-at (x +2)) (erase′ b s (t₂ U.[ ⟨ x +2 ≔ u ⟩ ]))
                [ T.sgSubst (wk (step-at x) (loop s)) T.⇑ ]              ≡⟨ cong₂ T._[_] (erase-≔ (there (there (x◂𝟘∈γ+δʳ refl erased))) ▸t₂)
                                                                              (cong T._⇑ $ cong T.sgSubst wk-loop) ⟩
              erase′ b s t₂ [ T.sgSubst (loop s) T.⇑ ]                   ∎))
          refl
          (erase-≔ (x◂𝟘∈pγ refl r≢𝟘 (x◂𝟘∈γ+δˡ refl erased))
             (▸-cong (≢𝟘→⌞⌟≡𝟙ᵐ r≢𝟘) ▸t₁))
        where
        open Tools.Reasoning.PropositionalEquality
    …   | no p≢𝟘 =
        cong₂ prodrec
          (erase-≔ (x◂𝟘∈pγ refl r≢𝟘 (x◂𝟘∈γ+δˡ refl erased))
             (▸-cong (≢𝟘→⌞⌟≡𝟙ᵐ r≢𝟘) ▸t₁))
          (erase-≔ (there (there (x◂𝟘∈γ+δʳ refl erased))) ▸t₂)
    erase-≔ {s} _ ℕₘ =
      wk-loop? s
    erase-≔ _ zeroₘ =
      refl
    erase-≔ {b} {s} {x} {u} erased (sucₘ {t} ▸t) =
      wk (step-at x) (suc⟨ s ⟩ (erase′ b s (t U.[ ⟨ x ≔ u ⟩ ])))  ≡⟨ wk-suc⟨⟩ ⟩
      suc⟨ s ⟩ (wk (step-at x) (erase′ b s (t U.[ ⟨ x ≔ u ⟩ ])))  ≡⟨ cong suc⟨ _ ⟩ $ erase-≔ erased ▸t ⟩
      suc⟨ s ⟩ (erase′ b s t)                                     ∎
      where
      open Tools.Reasoning.PropositionalEquality
    erase-≔
      {n = 1+ _} {x}
      erased (natrecₘ {γ} {δ} {p} {r} {η} ▸t₁ ▸t₂ ▸t₃ _) =
      cong₃ natrec
        (erase-≔
           (                                                          $⟨ erased ⟩
            x ◂ 𝟘 ∈ nrᶜ p r γ δ η                                     →⟨ ◂∈⇔ .proj₁ ⟩
            nrᶜ p r γ δ η ⟨ x ⟩ ≡ 𝟘                                   →⟨ trans (sym (nrᶜ-⟨⟩ γ)) ⟩
            nr p r (γ ⟨ x ⟩) (δ ⟨ x ⟩) (η ⟨ x ⟩) ≡ 𝟘                  →⟨ trans (update-lookup γ _) ⟩
            (γ , x ≔ nr p r (γ ⟨ x ⟩) (δ ⟨ x ⟩) (η ⟨ x ⟩)) ⟨ x ⟩ ≡ 𝟘  →⟨ ◂∈⇔ .proj₂ ⟩
            x ◂ 𝟘 ∈ γ , x ≔ nr p r (γ ⟨ x ⟩) (δ ⟨ x ⟩) (η ⟨ x ⟩)      □)
           (sub ▸t₁ $ begin
              γ , x ≔ nr p r (γ ⟨ x ⟩) (δ ⟨ x ⟩) (η ⟨ x ⟩)      ≤⟨ update-monotoneʳ _
                                                                     ($⟨ erased ⟩
                x ◂ 𝟘 ∈ nrᶜ p r γ δ η                                 →⟨ ◂𝟘∈nrᶜ₃ refl ⟩
                x ◂ 𝟘 ∈ η                                             →⟨ ◂∈⇔ .proj₁ ⟩
                η ⟨ x ⟩ ≡ 𝟘                                           →⟨ nr-zero ∘→ ≤-reflexive ⟩
                nr p r (γ ⟨ x ⟩) (δ ⟨ x ⟩) (η ⟨ x ⟩) ≤ γ ⟨ x ⟩        □) ⟩

              γ , x ≔ γ ⟨ x ⟩                                   ≡⟨ update-self _ _ ⟩

              γ                                                 ∎))
        (erase-≔ (there (there (◂𝟘∈nrᶜ₂ refl erased))) ▸t₂)
        (erase-≔ (◂𝟘∈nrᶜ₃ refl erased) ▸t₃)
      where
      open ≤ᶜ-reasoning
    erase-≔
      {n = 1+ _} erased (natrec-no-nrₘ ▸t₁ ▸t₂ ▸t₃ _ γ≤₁ _ γ≤₃ γ≤₄) =
      cong₃ natrec (erase-≔ erased (sub ▸t₁ γ≤₁))
        (erase-≔ (there (there (x◂𝟘∈γ+δˡ refl (x◂𝟘∈γ≤δ erased γ≤₄))))
           ▸t₂)
        (erase-≔ (x◂𝟘∈γ≤δ erased γ≤₃) ▸t₃)
    erase-≔
      {n = 1+ _} erased
      (natrec-no-nr-glbₘ {γ} {δ} {r} {χ} ▸t₁ ▸t₂ ▸t₃ _ glb χ-glb) =
      cong₃ natrec
        (erase-≔ (x◂𝟘∈γ+δʳ refl erased) $
         sub ▸t₁ $ begin
           χ             ≤⟨ χ-glb .proj₁ 0 ⟩
           nrᵢᶜ r γ δ 0  ≈⟨ nrᵢᶜ-zero ⟩
           γ             ∎)
        (erase-≔
           (_◂_∈_.there $ there $ x◂𝟘∈γ+δˡ refl $
            x◂𝟘∈γ≤δ (x◂𝟘∈γ+δʳ refl erased) $ begin
              χ                       ≤⟨ χ-glb .proj₁ 1 ⟩
              nrᵢᶜ r γ δ 1            ≈⟨ nrᵢᶜ-suc ⟩
              δ +ᶜ r ·ᶜ nrᵢᶜ r γ δ 0  ∎)
           ▸t₂)
        (erase-≔
           (x◂𝟘∈pγ refl (λ { refl → 𝟘≰𝟙 (glb .proj₁ 0) })
              (x◂𝟘∈γ+δˡ refl erased))
           ▸t₃)
      where
      open ≤ᶜ-reasoning
    erase-≔ {s} _ (Idₘ _ _ _ _) =
      wk-loop? s
    erase-≔ {s} _ (Id₀ₘ _ _ _ _) =
      wk-loop? s
    erase-≔ {s} _ rflₘ =
      wk-loop? s
    erase-≔ erased (Jₘ _ _ _ _ _ ▸t _ _) =
      erase-≔
        (x◂𝟘∈γ+δˡ refl $ x◂𝟘∈γ+δʳ refl $ x◂𝟘∈γ+δʳ refl $
         x◂𝟘∈pγ refl ω≢𝟘 erased)
        ▸t
    erase-≔ erased (J₀ₘ₁ _ _ _ _ _ _ ▸t _ _) =
      erase-≔ (x◂𝟘∈γ+δʳ refl $ x◂𝟘∈pγ refl ω≢𝟘 erased) ▸t
    erase-≔ erased (J₀ₘ₂ _ _ _ _ ▸t _ _) =
      erase-≔ erased ▸t
    erase-≔ erased (Kₘ _ _ _ _ _ ▸t _) =
      erase-≔
        (x◂𝟘∈γ+δˡ refl $ x◂𝟘∈γ+δʳ refl $ x◂𝟘∈γ+δʳ refl $
         x◂𝟘∈pγ refl ω≢𝟘 erased)
        ▸t
    erase-≔ erased (K₀ₘ₁ _ _ _ _ _ ▸t _) =
      erase-≔ (x◂𝟘∈γ+δʳ refl $ x◂𝟘∈pγ refl ω≢𝟘 erased) ▸t
    erase-≔ erased (K₀ₘ₂ _ _ _ _ ▸t _) =
      erase-≔ erased ▸t
    erase-≔ {s} _ ([]-congₘ _ _ _ _ _) =
      wk-loop? s

  opaque

    -- A special case of erase-≔.

    erase-[]₀ :
      ⦃ 𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet ⦄ →
      x0 ◂ 𝟘 ∈ γ → γ ▸[ 𝟙ᵐ ] t →
      T.wk1 (erase′ b s (t U.[ u ]₀)) ≡ erase′ b s t
    erase-[]₀ = erase-≔

  opaque

    -- A variant of erase-[]₀.

    erase-[wk1]↑ :
      ⦃ 𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet ⦄ →
      x0 ◂ 𝟘 ∈ γ → γ ▸[ 𝟙ᵐ ] t →
      erase′ b s (t U.[ U.wk1 u ]↑) ≡ erase′ b s t
    erase-[wk1]↑ {t} {b} {s} {u} x0◂ ▸t =
      erase′ b s (t U.[ U.wk1 u ]↑)    ≡˘⟨ PE.cong (erase′ _ _) $ UP.wk[]′[][]↑ 1 t ⟩
      erase′ b s (U.wk1 (t U.[ u ]₀))  ≡˘⟨ wk-erase-comm _ (t U.[ _ ]₀) ⟩
      T.wk1 (erase′ b s (t U.[ u ]₀))  ≡⟨ erase-[]₀ x0◂ ▸t ⟩
      erase′ b s t                     ∎
      where
      open Tools.Reasoning.PropositionalEquality

  opaque

    -- If the modality's zero is well-behaved, then erased variables do
    -- not occur after extraction.

    erased-hasX :
      ⦃ 𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet ⦄ →
      x ◂ 𝟘 ∈ γ → γ ▸[ 𝟙ᵐ ] t → ¬ HasX x (erase′ b s t)
    erased-hasX {x} {t} {b} {s} x∈ ▸t =
      HasX x (erase′ b s t)                                     →⟨ PE.subst (HasX _) (sym $ erase-≔ x∈ ▸t) ⟩
      HasX x (wk (step-at x) (erase′ b s (t U.[ ⟨ x ≔ ℕ ⟩ ])))  →⟨ ¬-HasX-wk-step-at ⟩
      ⊥                                                         □
