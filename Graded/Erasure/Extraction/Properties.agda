------------------------------------------------------------------------
-- Properties of the extraction function.
------------------------------------------------------------------------

open import Graded.Modality
open import Tools.PropositionalEquality as PE

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
open import Tools.Nat using (Nat; 1+) renaming (_+_ to _+ⁿ_)
open import Tools.Product
open import Tools.Relation
open import Tools.Sum using (inj₁; inj₂)

import Tools.Reasoning.Equivalence
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality

private
  variable
    b : Bool
    m n : Nat
    A t u v : U.Term n
    v₁ v₂ : T.Term n
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
    ∀ t q A → p PE.≡ 𝟘 →
    erase′ b s (U.unitrec p q t A u v) PE.≡ erase′ b s v
  unitrec-𝟘 {p} _ _ _ p≡𝟘 with is-𝟘? p
  … | yes _  = PE.refl
  … | no p≢𝟘 = ⊥-elim (p≢𝟘 p≡𝟘)

opaque

  unitrec-ω :
    ∀ t q A → p PE.≢ 𝟘 →
    erase′ b s (U.unitrec p q t A u v) PE.≡
    T.unitrec (erase′ b s u) (erase′ b s v)
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

  app-𝟘′-subst : v₁ T.⇒ v₂ → app-𝟘′ b s v₁ T.⇒ app-𝟘′ b s v₂
  app-𝟘′-subst {b = true}  v₁⇒v₂ = v₁⇒v₂
  app-𝟘′-subst {b = false} v₁⇒v₂ = app-subst v₁⇒v₂

-- The functions wk ρ/U.wk ρ and erase′ b s commute.

wk-erase-comm : (ρ : U.Wk m n) (t : U.Term n)
              → wk ρ (erase′ b s t) ≡ erase′ b s (U.wk ρ t)
wk-erase-comm _ (var _) = refl
wk-erase-comm {s} _ Level = wk-loop? s
wk-erase-comm {s} _ zeroᵘ = wk-loop? s
wk-erase-comm {s} _ (sucᵘ _) = wk-loop? s
wk-erase-comm {s} _ (_ maxᵘ _) = wk-loop? s
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
wk-erase-comm ρ (U.unitrec p _ _ _ t u)
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
subst-erase-comm {s} _ Level = loop?-[] s
subst-erase-comm {s} _ zeroᵘ = loop?-[] s
subst-erase-comm {s} _ (sucᵘ _) = loop?-[] s
subst-erase-comm {s} _ (_ maxᵘ _) = loop?-[] s
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
subst-erase-comm σ (U.unitrec p _ _ _ t u) with is-𝟘? p
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

module hasX (R : Usage-restrictions) where

  open MU R
  open MUP R
  open MUP𝟘 R

  open import Graded.Usage.Restrictions.Instance R

  -- If the modality's zero is well-behaved, then erased variables do
  -- not occur after extraction.

  erased-hasX :
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet ⦄ →
    x ◂ 𝟘 ∈ γ → γ ▸[ 𝟙ᵐ ] t → HasX x (erase′ b s t) → ⊥

  erased-hasX erased γ▸t@var varₓ =
    valid-var-usage γ▸t (var-usage-lookup erased)

  erased-hasX {b = false} erased (lamₘ γ▸t) (lamₓ hasX) =
    erased-hasX (there erased) γ▸t hasX
  erased-hasX {b = true} erased (lamₘ {p} γ▸t) hasX with is-𝟘? p
  erased-hasX {b = true} {s} erased (lamₘ γ▸t) hasX | yes _ =
    erased-hasX (there erased) γ▸t
      (HasX-[closed]₀→ loop-closed hasX)
  erased-hasX {b = true} erased (lamₘ γ▸t) (lamₓ hasX) | no _ =
    erased-hasX (there erased) γ▸t hasX

  erased-hasX erased (_∘ₘ_ {γ = γ} {δ = δ} {p = p} γ▸t δ▸u) hasX
    with is-𝟘? p
  erased-hasX {b = false} erased (γ▸t ∘ₘ _) (∘ₓˡ hasX) | yes _ =
    erased-hasX (x◂𝟘∈γ+δˡ refl erased) γ▸t hasX
  erased-hasX {b = false} {s} _ (_ ∘ₘ _) (∘ₓʳ hasX) | yes _ =
    loop?-closed s hasX
  erased-hasX {b = true} erased (γ▸t ∘ₘ _) hasX | yes _ =
    erased-hasX (x◂𝟘∈γ+δˡ refl erased) γ▸t hasX
  erased-hasX erased (_∘ₘ_ {γ = γ} {δ = δ} {_} γ▸t δ▸u) (∘ₓˡ hasX)
    | no _ =
    erased-hasX (x◂𝟘∈γ+δˡ refl erased) γ▸t hasX
  erased-hasX erased (_∘ₘ_ {γ = γ} {δ = δ} {_} γ▸t δ▸u) (∘ₓʳ hasX)
    | no p≢𝟘 =
    erased-hasX (x◂𝟘∈pγ refl p≢𝟘 (x◂𝟘∈γ+δʳ refl erased))
                (▸-cong (≢𝟘→⌞⌟≡𝟙ᵐ p≢𝟘) δ▸u) hasX

  erased-hasX erased (prodʷₘ {γ = γ} {p = p} {δ = δ} _ δ▸) hasX
    with is-𝟘? p
  ... | yes refl =
    erased-hasX
      (PE.subst (_ ◂ _ ∈_)
         (≈ᶜ→≡ (begin
            𝟘 ·ᶜ γ +ᶜ δ  ≈⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
            𝟘ᶜ +ᶜ δ      ≈⟨ +ᶜ-identityˡ _ ⟩
            δ            ∎))
         erased)
      δ▸ hasX
    where
    open Tools.Reasoning.Equivalence Conₘ-setoid
  erased-hasX {s = non-strict} erased (prodʷₘ γ▸ _) (prodₓˡ hasX)
    | no p≢𝟘 =
    erased-hasX (x◂𝟘∈pγ refl p≢𝟘 (x◂𝟘∈γ+δˡ refl erased))
                (▸-cong (≢𝟘→⌞⌟≡𝟙ᵐ p≢𝟘) γ▸) hasX
  erased-hasX {s = non-strict} erased (prodʷₘ _ δ▸) (prodₓʳ hasX)
    | no _ =
    erased-hasX (x◂𝟘∈γ+δʳ refl erased) δ▸ hasX
  erased-hasX
    {s = strict} _ (prodʷₘ _ _) (∘ₓˡ (∘ₓˡ (lamₓ (lamₓ (prodₓˡ ())))))
    | no _
  erased-hasX
    {s = strict} _ (prodʷₘ _ _) (∘ₓˡ (∘ₓˡ (lamₓ (lamₓ (prodₓʳ ())))))
    | no _
  erased-hasX {s = strict} erased (prodʷₘ γ▸ _) (∘ₓˡ (∘ₓʳ hasX))
    | no p≢𝟘 =
    erased-hasX (x◂𝟘∈pγ refl p≢𝟘 (x◂𝟘∈γ+δˡ refl erased))
      (▸-cong (≢𝟘→⌞⌟≡𝟙ᵐ p≢𝟘) γ▸) hasX
  erased-hasX {s = strict} erased (prodʷₘ _ δ▸) (∘ₓʳ hasX)
    | no _ =
    erased-hasX (x◂𝟘∈γ+δʳ refl erased) δ▸ hasX

  erased-hasX erased (prodˢₘ {γ = γ} {p = p} {δ = δ} _ γ▸u) hasX
    with is-𝟘? p
  ... | yes refl = erased-hasX (x◂𝟘∈γ∧δʳ refl erased) γ▸u hasX
  erased-hasX {s = non-strict} erased (prodˢₘ γ▸ _) (prodₓˡ hasX)
    | no p≢𝟘 =
    erased-hasX (x◂𝟘∈pγ refl p≢𝟘 (x◂𝟘∈γ∧δˡ refl erased))
                (▸-cong (≢𝟘→⌞⌟≡𝟙ᵐ p≢𝟘) γ▸) hasX
  erased-hasX {s = non-strict} erased (prodˢₘ _ δ▸) (prodₓʳ hasX)
    | no p≢𝟘 =
    erased-hasX erased (sub δ▸ (∧ᶜ-decreasingʳ _ _)) hasX
  erased-hasX
    {s = strict} _ (prodˢₘ _ _) (∘ₓˡ (∘ₓˡ (lamₓ (lamₓ (prodₓˡ ())))))
    | no _
  erased-hasX
    {s = strict} _ (prodˢₘ _ _) (∘ₓˡ (∘ₓˡ (lamₓ (lamₓ (prodₓʳ ())))))
    | no _
  erased-hasX {s = strict} erased (prodˢₘ γ▸ _) (∘ₓˡ (∘ₓʳ hasX))
    | no p≢𝟘 =
    erased-hasX (x◂𝟘∈pγ refl p≢𝟘 (x◂𝟘∈γ∧δˡ refl erased))
      (▸-cong (≢𝟘→⌞⌟≡𝟙ᵐ p≢𝟘) γ▸) hasX
  erased-hasX {s = strict} erased (prodˢₘ _ δ▸) (∘ₓʳ hasX)
    | no _ =
    erased-hasX (x◂𝟘∈γ∧δʳ refl erased) δ▸ hasX

  erased-hasX erased (fstₘ {p = p} _ _ _ _) hasX with is-𝟘? p
  erased-hasX erased (fstₘ         _ _ _ _) hasX | yes _ =
    loop-closed hasX
  erased-hasX erased (fstₘ {p = _} 𝟘ᵐ _ () _) (fstₓ hasX) | no _
  erased-hasX erased (fstₘ {p = _} 𝟙ᵐ γ▸ _ _) (fstₓ hasX) | no p≢𝟘 =
    erased-hasX erased (▸-cong (≢𝟘→⌞⌟≡𝟙ᵐ p≢𝟘) γ▸) hasX


  erased-hasX erased (sndₘ {p = p} γ▸) hasX with is-𝟘? p
  ... | yes _ = erased-hasX erased γ▸ hasX
  erased-hasX erased (sndₘ {p = _} γ▸) (sndₓ hasX) | no _ =
    erased-hasX erased γ▸ hasX

  erased-hasX erased (prodrecₘ {r = r} {p = p} ▸t ▸u _ _) hasX
    with is-𝟘? r
  erased-hasX erased (prodrecₘ ▸t ▸u _ _) hasX
    | yes _ =
    erased-hasX (there (there (x◂𝟘∈γ+δʳ refl erased))) ▸u
      (HasX-[closed,closed]→ loop-closed loop-closed hasX)
  ... | no _ with is-𝟘? p
  erased-hasX erased (prodrecₘ {u} _ ▸u _ _) (∘ₓˡ (lamₓ hasX))
    | no _ | yes _ =
    case HasX-[liftSubst]→ {t = erase′ _ _ u} hasX of λ where
      (inj₁ (() , _))
      (inj₂ (_ , refl , x0     , _    , has))  → loop-closed has
      (inj₂ (_ , refl , (_ +1) , hasX , varₓ)) →
        erased-hasX (there (there (x◂𝟘∈γ+δʳ refl erased))) ▸u hasX
  erased-hasX erased (prodrecₘ ▸t _ _ _) (∘ₓʳ hasX) | no r≢𝟘 | yes _ =
    erased-hasX (x◂𝟘∈pγ refl r≢𝟘 (x◂𝟘∈γ+δˡ refl erased))
      (▸-cong (≢𝟘→⌞⌟≡𝟙ᵐ r≢𝟘) ▸t) hasX
  erased-hasX erased (prodrecₘ ▸t ▸u _ _) (prodrecₓˡ hasX)
    | no r≢𝟘 | no _ =
    erased-hasX (x◂𝟘∈pγ refl r≢𝟘 (x◂𝟘∈γ+δˡ refl erased))
                (▸-cong (≢𝟘→⌞⌟≡𝟙ᵐ r≢𝟘) ▸t) hasX
  erased-hasX erased (prodrecₘ ▸t ▸u _ _) (prodrecₓʳ hasX)
    | no _ | no _ =
    erased-hasX (there (there (x◂𝟘∈γ+δʳ refl erased))) ▸u hasX

  erased-hasX {s = non-strict} erased (sucₘ γ▸t) (sucₓ hasX) =
    erased-hasX erased γ▸t hasX
  erased-hasX {s = strict} _ (sucₘ _) (∘ₓˡ (lamₓ (sucₓ ())))
  erased-hasX {s = strict} erased (sucₘ γ▸t) (∘ₓʳ hasX) =
    erased-hasX erased γ▸t hasX

  erased-hasX {x = x} erased
    (natrecₘ {γ = γ} {z = z} {δ = δ} {p = p} {r = r} {η = η}
       γ▸z δ▸s η▸n θ▸A)
    (natrecₓᶻ hasX) =
    erased-hasX erased′ lemma₃ hasX
      where
      erased′ =                                                   $⟨ erased ⟩
        x ◂ 𝟘 ∈ nrᶜ p r γ δ η                                     →⟨ ◂∈⇔ .proj₁ ⟩
        nrᶜ p r γ δ η ⟨ x ⟩ ≡ 𝟘                                   →⟨ trans (sym (nrᶜ-⟨⟩ γ)) ⟩
        nr p r (γ ⟨ x ⟩) (δ ⟨ x ⟩) (η ⟨ x ⟩) ≡ 𝟘                  →⟨ trans (update-lookup γ _) ⟩
        (γ , x ≔ nr p r (γ ⟨ x ⟩) (δ ⟨ x ⟩) (η ⟨ x ⟩)) ⟨ x ⟩ ≡ 𝟘  →⟨ ◂∈⇔ .proj₂ ⟩
        x ◂ 𝟘 ∈ γ , x ≔ nr p r (γ ⟨ x ⟩) (δ ⟨ x ⟩) (η ⟨ x ⟩)      □

      lemma₁ =                                          $⟨ erased ⟩
        x ◂ 𝟘 ∈ nrᶜ p r γ δ η                           →⟨ ◂𝟘∈nrᶜ₃ refl ⟩
        x ◂ 𝟘 ∈ η                                       →⟨ ◂∈⇔ .proj₁ ⟩
        η ⟨ x ⟩ ≡ 𝟘                                     →⟨ nr-zero ∘→ ≤-reflexive ⟩
        nr p r (γ ⟨ x ⟩) (δ ⟨ x ⟩) (η ⟨ x ⟩) ≤ γ ⟨ x ⟩  □

      lemma₂ = begin
        γ , x ≔ nr p r (γ ⟨ x ⟩) (δ ⟨ x ⟩) (η ⟨ x ⟩)  ≤⟨ update-monotoneʳ _ lemma₁ ⟩
        γ , x ≔ γ ⟨ x ⟩                               ≡⟨ update-self _ _ ⟩
        γ                                             ∎
        where
        open Tools.Reasoning.PartialOrder ≤ᶜ-poset

      lemma₃ : γ , x ≔ nr p r (γ ⟨ x ⟩) (δ ⟨ x ⟩) (η ⟨ x ⟩) ▸[ 𝟙ᵐ ] z
      lemma₃ = sub γ▸z lemma₂
  erased-hasX
    erased (natrec-no-nrₘ γ▸z _ _ _ χ≤γ _ _ _) (natrecₓᶻ hasX) =
    erased-hasX erased (sub γ▸z χ≤γ) hasX
  erased-hasX erased (natrec-no-nr-glbₘ ▸z _ _ _ _ χ-glb) (natrecₓᶻ hasX) =
    erased-hasX (x◂𝟘∈γ+δʳ refl erased)
      (sub ▸z (≤ᶜ-trans (χ-glb .proj₁ 0) (≤ᶜ-reflexive nrᵢᶜ-zero))) hasX
  erased-hasX erased (natrecₘ _ δ▸s _ _) (natrecₓˢ hasX) =
    erased-hasX (there (there (◂𝟘∈nrᶜ₂ refl erased))) δ▸s hasX
  erased-hasX erased
    (natrec-no-nrₘ _ δ▸s _ _ _ _ _ fix)
    (natrecₓˢ hasX) =
    erased-hasX
      (there $ there $ x◂𝟘∈γ+δˡ refl $ x◂𝟘∈γ≤δ erased fix)
      δ▸s hasX
  erased-hasX erased (natrec-no-nr-glbₘ _ ▸s _ _ _ χ-glb) (natrecₓˢ hasX) =
    erased-hasX (there $ there $ x◂𝟘∈γ+δˡ refl $
                   x◂𝟘∈γ≤δ (x◂𝟘∈γ+δʳ refl erased)
                   (≤ᶜ-trans (χ-glb .proj₁ 1) (≤ᶜ-reflexive nrᵢᶜ-suc)))
      ▸s hasX
  erased-hasX erased (natrecₘ _ _ η▸n _) (natrecₓⁿ hasX) =
    erased-hasX (◂𝟘∈nrᶜ₃ refl erased) η▸n hasX
  erased-hasX erased
    (natrec-no-nrₘ _ _ η▸n _ _ _ χ≤η _)
    (natrecₓⁿ hasX) =
    erased-hasX (x◂𝟘∈γ≤δ erased χ≤η) η▸n hasX
  erased-hasX erased (natrec-no-nr-glbₘ _ _ ▸n _ x-glb _) (natrecₓⁿ hasX) =
    erased-hasX (x◂𝟘∈pγ refl (λ {refl → 𝟘≰𝟙 (x-glb .proj₁ 0)})
                        (x◂𝟘∈γ+δˡ refl erased))
                ▸n hasX

  erased-hasX erased (Jₘ _ _ _ _ _ ▸u _ _) hasX =
    erased-hasX
      (x◂𝟘∈γ+δˡ refl $ x◂𝟘∈γ+δʳ refl $ x◂𝟘∈γ+δʳ refl $
       x◂𝟘∈pγ refl ω≢𝟘 erased)
      ▸u hasX
  erased-hasX erased (J₀ₘ₁ _ _ _ _ _ _ ▸u _ _) hasX =
    erased-hasX (x◂𝟘∈γ+δʳ refl $ x◂𝟘∈pγ refl ω≢𝟘 erased) ▸u hasX
  erased-hasX erased (J₀ₘ₂ _ _ _ _ ▸u _ _) hasX =
    erased-hasX erased ▸u hasX
  erased-hasX erased (Kₘ _ _ _ _ _ ▸u _) hasX =
    erased-hasX
      (x◂𝟘∈γ+δˡ refl $ x◂𝟘∈γ+δʳ refl $ x◂𝟘∈γ+δʳ refl $
       x◂𝟘∈pγ refl ω≢𝟘 erased)
      ▸u hasX
  erased-hasX erased (K₀ₘ₁ _ _ _ _ _ ▸u _) hasX =
    erased-hasX (x◂𝟘∈γ+δʳ refl $ x◂𝟘∈pγ refl ω≢𝟘 erased) ▸u hasX
  erased-hasX erased (K₀ₘ₂ _ _ _ _ ▸u _) hasX =
    erased-hasX erased ▸u hasX

  erased-hasX erased (unitrecₘ {p} _ _ _ _ _) hasX
    with is-𝟘? p
  erased-hasX erased (unitrecₘ _ _ _ ▸v _) hasX | yes _ =
    erased-hasX (x◂𝟘∈γ+δʳ refl erased) ▸v hasX
  erased-hasX erased (unitrecₘ _ _ ▸u _ _) (unitrecₓˡ hasX) | no p≢𝟘 =
    erased-hasX (x◂𝟘∈pγ refl p≢𝟘 (x◂𝟘∈γ+δˡ refl erased))
                (▸-cong (≢𝟘→⌞⌟≡𝟙ᵐ p≢𝟘) ▸u) hasX
  erased-hasX erased (unitrecₘ _ _ _ ▸v _) (unitrecₓʳ hasX) | no _ =
    erased-hasX (x◂𝟘∈γ+δʳ refl erased) ▸v hasX

  erased-hasX _ (emptyrecₘ _ _ _) =
    loop-closed

  erased-hasX erased (sub δ▸t γ≤δ) hasX =
    erased-hasX (x◂𝟘∈γ≤δ erased γ≤δ) δ▸t hasX

  erased-hasX {s} _ Levelₘ               = loop?-closed s
  erased-hasX {s} _ zeroᵘₘ               = loop?-closed s
  erased-hasX {s} _ (sucᵘₘ _)            = loop?-closed s
  erased-hasX {s} _ (maxᵘₘ _ _)          = loop?-closed s
  erased-hasX {s} _ (Uₘ _)               = loop?-closed s
  erased-hasX {s} _ ℕₘ                   = loop?-closed s
  erased-hasX {s} _ Emptyₘ               = loop?-closed s
  erased-hasX {s} _ (Unitₘ _)            = loop?-closed s
  erased-hasX {s} _ (ΠΣₘ _ _)            = loop?-closed s
  erased-hasX {s} _ (Idₘ _ _ _ _)        = loop?-closed s
  erased-hasX {s} _ (Id₀ₘ _ _ _ _)       = loop?-closed s
  erased-hasX {s} _ rflₘ                 = loop?-closed s
  erased-hasX {s} _ ([]-congₘ _ _ _ _ _) = loop?-closed s

  erased-hasX _ (starʷₘ _)   ()
  erased-hasX _ (starˢₘ _ _) ()
  erased-hasX _ zeroₘ        ()
