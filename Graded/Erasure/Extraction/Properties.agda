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
    𝕋 𝕌 : Set _
    A A₁ A₂ t t₁ t₂ t₃ t₄ t₅ u : U.Term n
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
    ∀ q A → p PE.≡ 𝟘 →
    erase′ b s (U.unitrec p q A t u) PE.≡ erase′ b s u
  unitrec-𝟘 {p} _ _ p≡𝟘 with is-𝟘? p
  … | yes _  = PE.refl
  … | no p≢𝟘 = ⊥-elim (p≢𝟘 p≡𝟘)

opaque

  unitrec-ω :
    ∀ q A → p PE.≢ 𝟘 →
    erase′ b s (U.unitrec p q A t u) PE.≡
    T.unitrec (erase′ b s t) (erase′ b s u)
  unitrec-ω {p} _ _ p≢𝟘 with is-𝟘? p
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
  lam-≢𝟘 {p} _ _   with is-𝟘? p
  lam-≢𝟘     _ _   | no _    = refl
  lam-≢𝟘     _ p≢𝟘 | yes p≡𝟘 = ⊥-elim $ p≢𝟘 p≡𝟘

opaque

  lam-keep :
    (t : U.Term (1+ n)) →
    erase′ false s (U.lam p t) ≡ T.lam (erase′ false s t)
  lam-keep {p} _ with is-𝟘? p
  … | yes _ = refl
  … | no _  = refl

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
wk-erase-comm {s} _ Level = wk-loop? s
wk-erase-comm {s} _ zeroᵘ = wk-loop? s
wk-erase-comm {s} _ (sucᵘ _) = wk-loop? s
wk-erase-comm {s} _ (_ supᵘ _) = wk-loop? s
wk-erase-comm {s} _ (U _) = wk-loop? s
wk-erase-comm {s} _ (Lift _ _) = wk-loop? s
wk-erase-comm ρ (lift u) = wk-erase-comm ρ u
wk-erase-comm ρ (lower t) = wk-erase-comm ρ t
wk-erase-comm {s} _ (ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _) = wk-loop? s
wk-erase-comm _ (U.lam p _) with is-𝟘? p
wk-erase-comm ρ (U.lam _ t) | no _ =
  cong T.lam (wk-erase-comm (lift ρ) t)
wk-erase-comm {b = false} ρ (U.lam p t) | yes _ =
  cong T.lam (wk-erase-comm (lift ρ) t)
wk-erase-comm {b = true} {s} ρ (U.lam p t) | yes _ =
  wk ρ (erase′ true s t T.[ loop s ]₀)                ≡⟨ wk-β (erase′ _ _ t) ⟩
  wk (lift ρ) (erase′ true s t) T.[ wk ρ (loop s) ]₀  ≡⟨ cong (wk _ (erase′ _ _ t) T.[_]₀) wk-loop ⟩
  wk (lift ρ) (erase′ true s t) T.[ loop s ]₀         ≡⟨ cong T._[ _ ]₀ $ wk-erase-comm (lift ρ) t ⟩
  erase′ true s (U.wk (lift ρ) t) T.[ loop s ]₀       ∎
  where
  open Tools.Reasoning.PropositionalEquality
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
wk-erase-comm ρ (U.unitrec p _ _ t u)
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
wk-erase-comm {s} _ ([]-cong _ _ _ _ _ _) = wk-loop? s

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
subst-erase-comm {s} _ Level = loop?-[] s
subst-erase-comm {s} _ zeroᵘ = loop?-[] s
subst-erase-comm {s} _ (sucᵘ _) = loop?-[] s
subst-erase-comm {s} _ (_ supᵘ _) = loop?-[] s
subst-erase-comm {s} _ (U _) = loop?-[] s
subst-erase-comm {s} _ (Lift _ _) = loop?-[] s
subst-erase-comm σ (lift u) = subst-erase-comm σ u
subst-erase-comm σ (lower t) = subst-erase-comm σ t
subst-erase-comm {s} _ (ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _) = loop?-[] s
subst-erase-comm         _ (U.lam p _) with is-𝟘? p
subst-erase-comm {b} {s} σ (U.lam _ t) | no _ =
  cong T.lam
    (erase′ b s t T.[ liftSubst (eraseSubst′ b s σ) ]    ≡⟨ substVar-to-subst liftSubst-erase-comm (erase′ _ _ t) ⟩
     erase′ b s t T.[ eraseSubst′ b s (U.liftSubst σ) ]  ≡⟨ subst-erase-comm _ t ⟩
     erase′ b s (t U.[ U.liftSubst σ ])                  ∎)
  where
  open Tools.Reasoning.PropositionalEquality
subst-erase-comm {b = true} {s} σ (U.lam _ t) | yes _ =
  erase′ true s t T.[ loop s ]₀ T.[ (eraseSubst′ true s σ) ]            ≡⟨ singleSubstLift (erase′ _ _ t) _ ⟩

  erase′ true s t T.[ liftSubst (eraseSubst′ true s σ) ]
    T.[ loop s [ eraseSubst′ true s σ ] ]₀                              ≡⟨ cong (erase′ _ _ t T.[ liftSubst _ ] T.[_]₀) loop-[] ⟩

  erase′ true s t T.[ liftSubst (eraseSubst′ true s σ) ] T.[ loop s ]₀  ≡⟨ cong T._[ _ ]₀ $ substVar-to-subst liftSubst-erase-comm (erase′ _ _ t) ⟩

  erase′ true s t T.[ eraseSubst′ true s (U.liftSubst σ) ]
    T.[ loop s ]₀                                                       ≡⟨ cong T._[ _ ]₀ $ subst-erase-comm _ t ⟩

  erase′ true s (t U.[ U.liftSubst σ ]) T.[ loop s ]₀                   ∎
  where
  open Tools.Reasoning.PropositionalEquality
subst-erase-comm {b = false} {s} σ (U.lam _ t) | yes _ =
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
subst-erase-comm σ (U.unitrec p _ _ t u) with is-𝟘? p
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
subst-erase-comm {s} _ ([]-cong _ _ _ _ _ _) = loop?-[] s

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
  unfolding eraseDCon″

  -- Glassification does not affect the result of eraseDCon′.

  eraseDCon″-glassify :
    {erase : 𝕋 → 𝕌} {∇ : DCon 𝕋 n} →
    eraseDCon″ erase (glassify ∇) ≡ eraseDCon″ erase ∇
  eraseDCon″-glassify {∇ = ε}    = refl
  eraseDCon″-glassify {∇ = ∇ ∙!} =
    cong (_++ _) (eraseDCon″-glassify {∇ = ∇})

opaque
  unfolding eraseDCon′

  -- Glassification does not affect the result of eraseDCon′.

  eraseDCon-glassify :
    {∇ : DCon (U.Term 0) n} →
    eraseDCon′ b s (glassify ∇) ≡ eraseDCon′ b s ∇
  eraseDCon-glassify {∇} = eraseDCon″-glassify {∇ = ∇}

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
    PE.subst (λ t → ¬ ∇ ⊢ t ∘⟨ s ⟩ loop? s ⇒* v)
      (lam (var x0 ∘⟨ s ⟩ loop? s)                    ≡˘⟨ PE.cong lam ∘-𝟘 ⟩
       lam (erase′ false s (var x0 ∘⟨ 𝟘 ⟩ var x0))    ≡˘⟨ lam-keep _ ⟩
       erase′ false s (lam 𝟘 (var x0 ∘⟨ 𝟘 ⟩ var x0))  ∎)
      (lemma _)
    where
    open Tools.Reasoning.PropositionalEquality

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

  private

    -- A definition used in the proof of erase-[].

    OK : U.Subst n n → Conₘ n → Set a
    OK σ γ = ∀ {x} → σ x ≢ var x → x ◂ 𝟘 ∈ γ

  private opaque

    -- Some lemmas used in the proof of erase-[].

    ¬◂𝟘∈,≔𝟙 :
      ⦃ 𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet ⦄ →
      ¬ x ◂ 𝟘 ∈ (γ , x ≔ 𝟙)
    ¬◂𝟘∈,≔𝟙 {x} {γ} =
      x ◂ 𝟘 ∈ (γ , x ≔ 𝟙)    ⇔⟨ ◂∈⇔ ⟩→
      (γ , x ≔ 𝟙) ⟨ x ⟩ ≡ 𝟘  ≡⟨ cong (_≡ _) $ update-lookup γ x ⟩→
      𝟙 ≡ 𝟘                  →⟨ non-trivial ⟩
      ⊥                      □

    erase-[]-var :
      ⦃ 𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet ⦄
      (y : Fin n) →
      OK σ (𝟘ᶜ , y ≔ 𝟙) →
      erase′ b s (σ y) ≡ var y
    erase-[]-var {σ} {b} {s} y ok
      with σ y | ok {x = y} | UP.is-var? (σ y)
    … | _ | ok | UP.not-var ≢var =
      ⊥-elim $ ¬◂𝟘∈,≔𝟙 $ ok ≢var
    … | _ | ok | UP.var x with x ≟ⱽ y
    …  | yes x≡y = cong var x≡y
    …  | no x≢y  =
      ⊥-elim $ ¬◂𝟘∈,≔𝟙 $ ok (x≢y ∘→ UP.var-PE-injectivity)

    OK-⇑-∙ : OK σ γ → OK (σ U.⇑) (γ ∙ p)
    OK-⇑-∙ _      {x = x0}   ≢var = ⊥-elim $ ≢var refl
    OK-⇑-∙ erased {x = _ +1} ≢var =
      there (erased (≢var ∘→ cong U.wk1))

  opaque

    -- Substituting anything for erasable variables (using a
    -- substitution of type U.Subst n n) does not affect the result of
    -- erasure (assuming that the modality has a well-behaved zero).

    erase-[] :
      {σ : U.Subst n n}
      ⦃ 𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet ⦄ →
      (∀ {x} → σ x ≢ var x → x ◂ 𝟘 ∈ γ) →
      γ ▸[ 𝟙ᵐ ] t →
      erase′ b s (t U.[ σ ]) ≡ erase′ b s t
    erase-[] ok (sub ▸t γ≤δ) =
      erase-[] (flip x◂𝟘∈γ≤δ γ≤δ ∘→ ok) ▸t
    erase-[] ok var =
      erase-[]-var _ ok
    erase-[] _ defn =
      refl
    erase-[] _ Levelₘ =
      refl
    erase-[] _ zeroᵘₘ =
      refl
    erase-[] _ (sucᵘₘ _) =
      refl
    erase-[] _ (supᵘₘ _ _) =
      refl
    erase-[] _ (Uₘ _) =
      refl
    erase-[] _ (Liftₘ _ _) =
      refl
    erase-[] ok (liftₘ ▸t) =
      erase-[] ok ▸t
    erase-[] ok (lowerₘ ▸t) =
      erase-[] ok ▸t
    erase-[] _ Emptyₘ =
      refl
    erase-[] _ (emptyrecₘ _ _ _) =
      refl
    erase-[] _ Unitₘ =
      refl
    erase-[] _ (starˢₘ _) =
      refl
    erase-[] _ starʷₘ =
      refl
    erase-[] ok (unitrecₘ {p} _ ▸t₁ ▸t₂ _) with is-𝟘? p
    … | no p≢𝟘 =
      cong₂ unitrec
        (erase-[] (x◂𝟘∈pγ refl p≢𝟘 ∘→ x◂𝟘∈γ+δˡ refl ∘→ ok)
           (▸-cong (≢𝟘→⌞⌟≡𝟙ᵐ p≢𝟘) ▸t₁))
        (erase-[] (x◂𝟘∈γ+δʳ refl ∘→ ok) ▸t₂)
    … | yes _ =
      erase-[] (x◂𝟘∈γ+δʳ refl ∘→ ok) ▸t₂
    erase-[] _ (ΠΣₘ _ _) =
      refl
    erase-[] ok (lamₘ {p} ▸t) with is-𝟘? p
    … | no _ =
      cong lam (erase-[] (OK-⇑-∙ ok) ▸t)
    erase-[] {b = false} ok (lamₘ ▸t) | yes _ =
      cong lam (erase-[] (OK-⇑-∙ ok) ▸t)
    erase-[] {b = true} ok (lamₘ ▸t) | yes _ =
      cong T._[ _ ]₀ (erase-[] (OK-⇑-∙ ok) ▸t)
    erase-[] ok (_∘ₘ_ {p} ▸t ▸u) with is-𝟘? p
    … | no p≢𝟘 =
      cong₂ _∘⟨ _ ⟩_ (erase-[] (x◂𝟘∈γ+δˡ refl ∘→ ok) ▸t)
        (erase-[] (x◂𝟘∈pγ refl p≢𝟘 ∘→ x◂𝟘∈γ+δʳ refl ∘→ ok)
           (▸-cong (≢𝟘→⌞⌟≡𝟙ᵐ p≢𝟘) ▸u))
    erase-[] {b = false} ok (▸t ∘ₘ _) | yes _ =
      cong (_∘⟨ _ ⟩ _) (erase-[] (x◂𝟘∈γ+δˡ refl ∘→ ok) ▸t)
    erase-[] {b = true} ok (▸t ∘ₘ _) | yes _ =
      erase-[] (x◂𝟘∈γ+δˡ refl ∘→ ok) ▸t
    erase-[] ok (prodˢₘ {p} ▸t₁ ▸t₂) with is-𝟘? p
    … | yes _ =
      erase-[] (x◂𝟘∈γ∧δʳ refl ∘→ ok) ▸t₂
    … | no p≢𝟘 =
      cong₂ prod⟨ _ ⟩
        (erase-[] (x◂𝟘∈pγ refl p≢𝟘 ∘→ x◂𝟘∈γ∧δˡ refl ∘→ ok)
           (▸-cong (≢𝟘→⌞⌟≡𝟙ᵐ p≢𝟘) ▸t₁))
        (erase-[] (x◂𝟘∈γ∧δʳ refl ∘→ ok) ▸t₂)
    erase-[] ok (fstₘ {p} _ ▸t eq _) with is-𝟘? p
    … | yes _ =
      refl
    … | no _ =
      cong fst (erase-[] ok (▸-cong eq ▸t))
    erase-[] ok (sndₘ {p} ▸t) with is-𝟘? p
    … | yes _ =
      erase-[] ok ▸t
    … | no _ =
      cong snd (erase-[] ok ▸t)
    erase-[] ok (prodʷₘ {p} ▸t₁ ▸t₂) with is-𝟘? p
    … | yes _ =
      erase-[] (x◂𝟘∈γ+δʳ refl ∘→ ok) ▸t₂
    … | no p≢𝟘 =
      cong₂ prod⟨ _ ⟩
        (erase-[] (x◂𝟘∈pγ refl p≢𝟘 ∘→ x◂𝟘∈γ+δˡ refl ∘→ ok)
           (▸-cong (≢𝟘→⌞⌟≡𝟙ᵐ p≢𝟘) ▸t₁))
        (erase-[] (x◂𝟘∈γ+δʳ refl ∘→ ok) ▸t₂)
    erase-[] ok (prodrecₘ {r} ▸t₁ ▸t₂ _ _) with is-𝟘? r
    … | yes _ =
      cong _[ _ , _ ]₁₀
        (erase-[] (OK-⇑-∙ $ OK-⇑-∙ $ x◂𝟘∈γ+δʳ refl ∘→ ok) ▸t₂)
    … | no r≢𝟘 =
      cong₂ (erase-prodrecω _ _)
        (erase-[] (x◂𝟘∈pγ refl r≢𝟘 ∘→ x◂𝟘∈γ+δˡ refl ∘→ ok)
           (▸-cong (≢𝟘→⌞⌟≡𝟙ᵐ r≢𝟘) ▸t₁))
        (erase-[] (OK-⇑-∙ $ OK-⇑-∙ $ x◂𝟘∈γ+δʳ refl ∘→ ok) ▸t₂)
    erase-[] _ ℕₘ =
      refl
    erase-[] _ zeroₘ =
      refl
    erase-[] ok (sucₘ ▸t) =
      cong suc⟨ _ ⟩ (erase-[] ok ▸t)
    erase-[] ok (natrecₘ {γ} {δ} {p} {r} {η} ▸t₁ ▸t₂ ▸t₃ _) =
      cong₃ natrec
        (erase-[]
           (λ {x = x} σx≢var-x →
              let x◂𝟘 = ok σx≢var-x in
                                                                        $⟨ x◂𝟘 ⟩
              x ◂ 𝟘 ∈ nrᶜ p r γ δ η                                     →⟨ ◂∈⇔ .proj₁ ⟩

              nrᶜ p r γ δ η ⟨ x ⟩ ≡ 𝟘                                   →⟨ trans (sym (nrᶜ-⟨⟩ γ)) ⟩

              nr p r (γ ⟨ x ⟩) (δ ⟨ x ⟩) (η ⟨ x ⟩) ≡ 𝟘                  →⟨ trans (update-lookup γ _) ⟩

              (γ , x ≔ nr p r (γ ⟨ x ⟩) (δ ⟨ x ⟩) (η ⟨ x ⟩)) ⟨ x ⟩ ≡ 𝟘  →⟨ ◂∈⇔ .proj₂ ⟩

              x ◂ 𝟘 ∈ γ , x ≔ nr p r (γ ⟨ x ⟩) (δ ⟨ x ⟩) (η ⟨ x ⟩)      →⟨ flip x◂𝟘∈γ≤δ $ begin

                 γ , x ≔ nr p r (γ ⟨ x ⟩) (δ ⟨ x ⟩) (η ⟨ x ⟩)                ≤⟨ update-monotoneʳ _
                                                                                  ($⟨ x◂𝟘 ⟩
                   x ◂ 𝟘 ∈ nrᶜ p r γ δ η                                           →⟨ ◂𝟘∈nrᶜ₃ refl ⟩
                   x ◂ 𝟘 ∈ η                                                       →⟨ ◂∈⇔ .proj₁ ⟩
                   η ⟨ x ⟩ ≡ 𝟘                                                     →⟨ nr-zero ∘→ ≤-reflexive ⟩
                   nr p r (γ ⟨ x ⟩) (δ ⟨ x ⟩) (η ⟨ x ⟩) ≤ γ ⟨ x ⟩                  □) ⟩

                 γ , x ≔ γ ⟨ x ⟩                                             ≡⟨ update-self _ _ ⟩

                 γ                                                           ∎ ⟩

              x ◂ 𝟘 ∈ γ                                                 □)
           ▸t₁)
        (erase-[] (OK-⇑-∙ $ OK-⇑-∙ $ ◂𝟘∈nrᶜ₂ refl ∘→ ok) ▸t₂)
        (erase-[] (◂𝟘∈nrᶜ₃ refl ∘→ ok) ▸t₃)
      where
      open ≤ᶜ-reasoning
    erase-[] ok (natrec-no-nrₘ ▸t₁ ▸t₂ ▸t₃ _ γ≤₁ _ γ≤₃ γ≤₄) =
      cong₃ natrec (erase-[] ok (sub ▸t₁ γ≤₁))
        (erase-[]
           (OK-⇑-∙ $ OK-⇑-∙ $ x◂𝟘∈γ+δˡ refl ∘→ flip x◂𝟘∈γ≤δ γ≤₄ ∘→ ok)
           ▸t₂)
        (erase-[] (flip x◂𝟘∈γ≤δ γ≤₃ ∘→ ok) ▸t₃)
    erase-[]
      ok (natrec-no-nr-glbₘ {γ} {δ} {r} {χ} ▸t₁ ▸t₂ ▸t₃ _ glb χ-glb) =
      cong₃ natrec
        (erase-[] (x◂𝟘∈γ+δʳ refl ∘→ ok) $
         sub ▸t₁ $ begin
           χ             ≤⟨ χ-glb .proj₁ 0 ⟩
           nrᵢᶜ r γ δ 0  ≈⟨ nrᵢᶜ-zero ⟩
           γ             ∎)
        (erase-[]
           (OK-⇑-∙ $ OK-⇑-∙ $ x◂𝟘∈γ+δˡ refl ∘→
            flip x◂𝟘∈γ≤δ
              (begin
                 χ                       ≤⟨ χ-glb .proj₁ 1 ⟩
                 nrᵢᶜ r γ δ 1            ≈⟨ nrᵢᶜ-suc ⟩
                 δ +ᶜ r ·ᶜ nrᵢᶜ r γ δ 0  ∎) ∘→
            x◂𝟘∈γ+δʳ refl ∘→ ok)
           ▸t₂)
        (erase-[]
           (x◂𝟘∈pγ refl (λ { refl → 𝟘≰𝟙 (glb .proj₁ 0) }) ∘→
            x◂𝟘∈γ+δˡ refl ∘→ ok)
           ▸t₃)
      where
      open ≤ᶜ-reasoning
    erase-[] _ (Idₘ _ _ _ _) =
      refl
    erase-[] _ (Id₀ₘ _ _ _ _) =
      refl
    erase-[] _ rflₘ =
      refl
    erase-[] ok (Jₘ _ _ _ _ _ ▸t _ _) =
      erase-[]
        (x◂𝟘∈γ+δˡ refl ∘→ x◂𝟘∈γ+δʳ refl ∘→ x◂𝟘∈γ+δʳ refl ∘→
         x◂𝟘∈pγ refl ω≢𝟘 ∘→ ok)
        ▸t
    erase-[] ok (J₀ₘ₁ _ _ _ _ _ _ ▸t _ _) =
      erase-[] (x◂𝟘∈γ+δʳ refl ∘→ x◂𝟘∈pγ refl ω≢𝟘 ∘→ ok) ▸t
    erase-[] ok (J₀ₘ₂ _ _ _ _ ▸t _ _) =
      erase-[] ok ▸t
    erase-[] ok (Kₘ _ _ _ _ _ ▸t _) =
      erase-[]
        (x◂𝟘∈γ+δˡ refl ∘→ x◂𝟘∈γ+δʳ refl ∘→ x◂𝟘∈γ+δʳ refl ∘→
         x◂𝟘∈pγ refl ω≢𝟘 ∘→ ok)
        ▸t
    erase-[] ok (K₀ₘ₁ _ _ _ _ _ ▸t _) =
      erase-[] (x◂𝟘∈γ+δʳ refl ∘→ x◂𝟘∈pγ refl ω≢𝟘 ∘→ ok) ▸t
    erase-[] ok (K₀ₘ₂ _ _ _ _ ▸t _) =
      erase-[] ok ▸t
    erase-[] _ ([]-congₘ _ _ _ _ _ _) =
      refl

  opaque

    -- A variant of erase-[] with a closing substitution.

    wk₀-erase-[] :
      {σ : U.Subst 0 n}
      ⦃ 𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet ⦄ →
      𝟘ᶜ ▸[ 𝟙ᵐ ] t →
      T.wk wk₀ (erase′ b s (t U.[ σ ])) ≡ erase′ b s t
    wk₀-erase-[] {t} {b} {s} {σ} ▸t =
      T.wk wk₀ (erase′ b s (t U.[ σ ]))  ≡⟨ wk-erase-comm _ (t U.[ _ ]) ⟩
      erase′ b s (U.wk wk₀ (t U.[ σ ]))  ≡⟨ cong (erase′ _ _) $ UP.wk-subst t ⟩
      erase′ b s (t U.[ wk₀ U.•ₛ σ ])    ≡⟨ erase-[] (λ {x = x} _ → ◂∈⇔ .proj₂ (𝟘ᶜ-lookup x)) ▸t ⟩
      erase′ b s t                       ∎
      where
      open Tools.Reasoning.PropositionalEquality

  opaque

    -- A variant of erase-[] stated using ⟨_≔_⟩↑.

    erase-≔↑ :
      ⦃ 𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet ⦄ →
      x ◂ 𝟘 ∈ γ → γ ▸[ 𝟙ᵐ ] t →
      erase′ b s (t U.[ ⟨ x ≔ u ⟩↑ ]) ≡ erase′ b s t
    erase-≔↑ x◂ ▸t = erase-[] (flip (lemma _ _) x◂) ▸t
      where
      lemma :
        ∀ (x y : Fin n) {u} →
        ⟨ x ≔ u ⟩↑ y ≢ var y → x ◂ 𝟘 ∈ γ → y ◂ 𝟘 ∈ γ
      lemma x0 x0 _ x◂𝟘 =
        x◂𝟘
      lemma x0 (_ +1) ≢var =
        ⊥-elim $ ≢var refl
      lemma (_+1 {n = 0}    ())
      lemma (_+1 {n = 1+ _} x)  x0 ≢var =
        ⊥-elim $ ≢var refl
      lemma (_+1 {n = 1+ _} x) (y +1) ≢var (there x◂𝟘) =
        there (lemma x y (≢var ∘→ cong U.wk1) x◂𝟘)

  opaque

    -- A special case of erase-≔↑.

    erase-[]↑ :
      ⦃ 𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet ⦄ →
      x0 ◂ 𝟘 ∈ γ → γ ▸[ 𝟙ᵐ ] t →
      erase′ b s (t U.[ u ]↑) ≡ erase′ b s t
    erase-[]↑ = erase-≔↑

  opaque

    -- A variant of erase-≔↑.

    erase-≔ :
      ⦃ 𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet ⦄ →
      x ◂ 𝟘 ∈ γ → γ ▸[ 𝟙ᵐ ] t →
      wk (step-at x) (erase′ b s (t U.[ ⟨ x ≔ u ⟩ ])) ≡ erase′ b s t
    erase-≔ {x} {t} {b} {s} {u} x◂ ▸t =
      wk (step-at x) (erase′ b s (t U.[ ⟨ x ≔ u ⟩ ]))     ≡⟨ wk-erase-comm _ (t U.[ _ ]) ⟩
      erase′ b s (U.wk (step-at x) (t U.[ ⟨ x ≔ u ⟩ ]))   ≡⟨ PE.cong (erase′ _ _) $ UP.wk-subst t ⟩
      erase′ b s (t U.[ step-at x U.•ₛ ⟨ x ≔ u ⟩ ])       ≡⟨⟩
      erase′ b s (t U.[ U.wk (step-at x) ∘→ ⟨ x ≔ u ⟩ ])  ≡⟨ PE.cong (erase′ _ _) $ UP.substVar-to-subst UP.⟨≔⟩≡⟨≔⟩↑ t ⟩
      erase′ b s (t U.[ ⟨ x ≔ U.wk (step-at′ x) u ⟩↑ ])   ≡⟨ erase-≔↑ x◂ ▸t ⟩
      erase′ b s t                                        ∎
      where
      open Tools.Reasoning.PropositionalEquality

  opaque

    -- A special case of erase-≔.

    erase-[]₀ :
      ⦃ 𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet ⦄ →
      x0 ◂ 𝟘 ∈ γ → γ ▸[ 𝟙ᵐ ] t →
      T.wk1 (erase′ b s (t U.[ u ]₀)) ≡ erase′ b s t
    erase-[]₀ = erase-≔

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
