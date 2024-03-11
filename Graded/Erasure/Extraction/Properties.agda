------------------------------------------------------------------------
-- Properties of the extraction function.
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

open import Graded.Modality
open import Tools.PropositionalEquality as PE

module Graded.Erasure.Extraction.Properties
  {a} {M : Set a} (𝕄 : Modality M)
  (open Modality 𝕄)
  ⦃ 𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet ⦄
  where

open import Graded.Modality.Dedicated-nr.Instance
open import Graded.Modality.Nr-instances
open import Graded.Modality.Properties 𝕄

open import Graded.Erasure.Extraction 𝕄 is-𝟘?
open import Graded.Erasure.Target as T
  hiding (refl; trans)
  renaming (_[_,_] to _[_,_]₁₀)
open import Graded.Erasure.Target.Non-terminating
open import Graded.Erasure.Target.Properties

open import Definition.Untyped M as U
  hiding (Term; wk; _[_]; liftSubst)
  renaming (_[_,_] to _[_,_]U₁₀)

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
import Graded.Usage 𝕄 as MU
import Graded.Usage.Properties 𝕄 as MUP
import Graded.Usage.Properties.Has-well-behaved-zero 𝕄 as MUP𝟘
open import Graded.Usage.Restrictions 𝕄
open import Graded.Mode 𝕄

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
    m n : Nat
    t u A : U.Term n
    σ : U.Subst m n
    σ′ : T.Subst m n
    γ : Conₘ n
    x : Fin n
    p q r : M
    k : Strength
    s : Strictness

-- Lemmata on how erase computes

prod-𝟘 : p PE.≡ 𝟘
       → erase s (U.prod k p t u) PE.≡ erase s u
prod-𝟘 {p = p} p≡𝟘 with is-𝟘? p
... | yes p≡𝟘 = PE.refl
... | no p≢𝟘 = ⊥-elim (p≢𝟘 p≡𝟘)

prod-ω : p PE.≢ 𝟘
       → erase s (U.prod k p t u) PE.≡ T.prod (erase s t) (erase s u)
prod-ω {p = p} p≢𝟘 with is-𝟘? p
... | yes p≡𝟘 = ⊥-elim (p≢𝟘 p≡𝟘)
... | no p≢𝟘 = PE.refl

snd-𝟘 : p PE.≡ 𝟘
      → erase s (U.snd p t) PE.≡ erase s t
snd-𝟘 {p = p} p≡𝟘 with is-𝟘? p
... | yes p≡𝟘 = PE.refl
... | no p≢𝟘 = ⊥-elim (p≢𝟘 p≡𝟘)

snd-ω : p PE.≢ 𝟘
      → erase s (U.snd p t) PE.≡ T.snd (erase s t)
snd-ω {p = p} p≢𝟘 with is-𝟘? p
... | yes p≡𝟘 = ⊥-elim (p≢𝟘 p≡𝟘)
... | no p≢𝟘 = PE.refl

prodrec-ω : ∀ p → r PE.≢ 𝟘
          → erase s (U.prodrec r p q A t u)
          PE.≡ erase-prodrecω s p (erase s t) (erase s u)
prodrec-ω {r} p r≢𝟘 with is-𝟘? r
... | yes r≡𝟘 = ⊥-elim (r≢𝟘 r≡𝟘)
... | no r≢𝟘 with is-𝟘? p
... | yes p≡𝟘 = PE.refl
... | no p≢𝟘 = PE.refl

-- The functions wk ρ/U.wk ρ and erase s commute.

wk-erase-comm : (ρ : U.Wk m n) (t : U.Term n)
              → wk ρ (erase s t) ≡ erase s (U.wk ρ t)
wk-erase-comm _ (var _) = refl
wk-erase-comm ρ U = refl
wk-erase-comm ρ (Π p , w ▷ F ▹ G) = refl
wk-erase-comm ρ (U.lam p t) =
  cong T.lam (wk-erase-comm (lift ρ) t)
wk-erase-comm ρ (t U.∘⟨ p ⟩ u) with is-𝟘? p
... | yes _ = cong (T._∘⟨ _ ⟩ ↯) (wk-erase-comm ρ t)
... | no _ = cong₂ T._∘⟨ _ ⟩_ (wk-erase-comm ρ t) (wk-erase-comm ρ u)
wk-erase-comm ρ (Σ _ , _ ▷ _ ▹ _) = refl
wk-erase-comm ρ (U.prod _ p t u) with is-𝟘? p
... | yes _ = wk-erase-comm ρ u
... | no _ = cong₂ T.prod (wk-erase-comm ρ t) (wk-erase-comm ρ u)
wk-erase-comm ρ (U.fst p t) with is-𝟘? p
... | yes _ = wk-loop
... | no _ = cong T.fst (wk-erase-comm ρ t)
wk-erase-comm ρ (U.snd p t) with is-𝟘? p
... | yes _ = wk-erase-comm ρ t
... | no _ = cong T.snd (wk-erase-comm ρ t)
wk-erase-comm {s} ρ (U.prodrec r p _ A t u) with is-𝟘? r
... | yes _ =
  wk ρ (erase s u [ ↯ , ↯ ]₁₀)                  ≡⟨ wk-β-doubleSubst _ (erase _ u) _ _ ⟩
  wk (lift (lift ρ)) (erase s u) [ ↯ , ↯ ]₁₀    ≡⟨ cong _[ _ , _ ]₁₀ $ wk-erase-comm _ u ⟩
  erase s (U.wk (lift (lift ρ)) u) [ ↯ , ↯ ]₁₀  ∎
  where
  open Tools.Reasoning.PropositionalEquality
... | no _ with is-𝟘? p
... | yes _ =
  T.lam (wk (lift ρ) (erase s u T.[ liftSubst (T.sgSubst ↯) ]))
    T.∘⟨ s ⟩ wk ρ (erase s t)                                             ≡⟨ cong (λ u → T.lam u T.∘⟨ _ ⟩ _) $
                                                                             wk-lift-β (erase _ u) ⟩
  T.lam (wk (lift (lift ρ)) (erase s u) T.[ liftSubst (T.sgSubst ↯) ])
    T.∘⟨ s ⟩ wk ρ (erase s t)                                             ≡⟨ cong₂ (λ u t → T.lam (u T.[ _ ]) T.∘⟨ _ ⟩ t)
                                                                               (wk-erase-comm _ u)
                                                                               (wk-erase-comm _ t) ⟩
  T.lam (erase s (U.wk (lift (lift ρ)) u) T.[ liftSubst (T.sgSubst ↯) ])
    T.∘⟨ s ⟩ erase s (U.wk ρ t)                                           ∎
  where
  open Tools.Reasoning.PropositionalEquality
... | no _ = cong₂ T.prodrec (wk-erase-comm ρ t)
                   (wk-erase-comm (lift (lift ρ)) u)
wk-erase-comm ρ ℕ = refl
wk-erase-comm ρ U.zero = refl
wk-erase-comm {s} ρ (U.suc t) =
  wk ρ (suc⟨ s ⟩ (erase s t))    ≡⟨ wk-suc⟨⟩ ⟩
  suc⟨ s ⟩ (wk ρ (erase s t))    ≡⟨ cong suc⟨ _ ⟩ (wk-erase-comm _ t) ⟩
  suc⟨ s ⟩ (erase s (U.wk ρ t))  ∎
  where
  open Tools.Reasoning.PropositionalEquality
wk-erase-comm ρ (U.natrec p q r A z s n) =
  cong₃ T.natrec (wk-erase-comm ρ z)
                 (wk-erase-comm (lift (lift ρ)) s)
                 (wk-erase-comm ρ n)
wk-erase-comm ρ Unit! = refl
wk-erase-comm ρ U.star! = refl
wk-erase-comm ρ (U.unitrec p q A t u)
  with is-𝟘? p
... | yes _ =
  wk-erase-comm _ u
... | no _ =
  cong₂ T.unitrec (wk-erase-comm ρ t)
                  (wk-erase-comm ρ u)
wk-erase-comm ρ Empty = refl
wk-erase-comm _ (emptyrec _ _ _) = wk-loop
wk-erase-comm _ (Id _ _ _) = refl
wk-erase-comm _ U.rfl = refl
wk-erase-comm _ (J _ _ _ _ _ u _ _) = wk-erase-comm _ u
wk-erase-comm _ (K _ _ _ _ u _) = wk-erase-comm _ u
wk-erase-comm _ ([]-cong _ _ _ _ _) = refl

-- Lifting substitutions commute with erase

liftSubst-erase-comm :
  (x : Fin (1+ n)) →
  liftSubst (eraseSubst s σ) x ≡ eraseSubst s (U.liftSubst σ) x
liftSubst-erase-comm     x0     = refl
liftSubst-erase-comm {σ} (_ +1) = wk-erase-comm _ (σ _)

-- Multiple lifts commutes with erase

liftSubsts-erase-comm :
  (k : Nat) (x : Fin (k +ⁿ n)) →
  T.liftSubstn (eraseSubst s σ) k x ≡ eraseSubst s (U.liftSubstn σ k) x
liftSubsts-erase-comm 0 x = refl
liftSubsts-erase-comm (1+ k) x0 = refl
liftSubsts-erase-comm {s} {σ} (1+ k) (x +1) =
  T.wk1 (T.liftSubstn (eraseSubst s σ) k x)          ≡⟨ cong T.wk1 $ liftSubsts-erase-comm k _ ⟩
  T.wk1 (eraseSubst s (U.liftSubstn σ k) x)          ≡⟨⟩
  wk (step id) (eraseSubst s (U.liftSubstn σ k) x)   ≡⟨ wk-erase-comm _ (U.liftSubstn σ _ _) ⟩
  erase s (U.wk (U.step U.id) (U.liftSubstn σ k x))  ≡⟨⟩
  eraseSubst s (U.liftSubstn σ (1+ k)) (x +1)        ∎
  where
  open Tools.Reasoning.PropositionalEquality


-- Substitution commutes with erase s (modulo the translation of the
-- substitution to the target language).

subst-erase-comm :
  (σ : U.Subst m n) (t : U.Term n) →
  erase s t T.[ eraseSubst s σ ] ≡ erase s (t U.[ σ ])
subst-erase-comm σ (var x) = refl
subst-erase-comm σ U = refl
subst-erase-comm σ (Π p , q ▷ F ▹ G) = refl
subst-erase-comm {s} σ (U.lam p t) =
  cong Term.lam
    (erase s t T.[ liftSubst (eraseSubst s σ) ]    ≡⟨ substVar-to-subst (liftSubsts-erase-comm 1) (erase _ t) ⟩
     erase s t T.[ eraseSubst s (U.liftSubst σ) ]  ≡⟨ subst-erase-comm _ t ⟩
     erase s (t U.[ U.liftSubst σ ])               ∎)
  where
  open Tools.Reasoning.PropositionalEquality
subst-erase-comm σ (t U.∘⟨ p ⟩ u) with is-𝟘? p
... | yes _ = cong (T._∘⟨ _ ⟩ ↯) (subst-erase-comm σ t)
... | no _ =
  cong₂ T._∘⟨ _ ⟩_ (subst-erase-comm σ t) (subst-erase-comm σ u)
subst-erase-comm σ (ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _) = refl
subst-erase-comm σ (U.prod _ p t u) with is-𝟘? p
... | yes _ = subst-erase-comm σ u
... | no _ = cong₂ T.prod (subst-erase-comm σ t) (subst-erase-comm σ u)
subst-erase-comm σ (U.fst p t) with is-𝟘? p
... | yes _ = loop-[]
... | no _ = cong T.fst (subst-erase-comm σ t)
subst-erase-comm σ (U.snd p t) with is-𝟘? p
... | yes _ = subst-erase-comm σ t
... | no _  = cong T.snd (subst-erase-comm σ t)
subst-erase-comm {s} σ (U.prodrec r p _ A t u) with is-𝟘? r
... | yes _ =
  erase s u [ ↯ , ↯ ]₁₀ T.[ eraseSubst s σ ]                   ≡⟨ doubleSubstLift _ (erase _ u) _ _ ⟩
  erase s u T.[ T.liftSubstn (eraseSubst s σ) 2 ] [ ↯ , ↯ ]₁₀  ≡⟨ cong _[ _ , _ ]₁₀ $
                                                                  substVar-to-subst (liftSubsts-erase-comm 2) (erase _ u) ⟩
  erase s u T.[ eraseSubst s (U.liftSubstn σ 2) ] [ ↯ , ↯ ]₁₀  ≡⟨ cong _[ _ , _ ]₁₀ $
                                                                  subst-erase-comm _ u ⟩
  erase s (u U.[ U.liftSubstn σ 2 ]) [ ↯ , ↯ ]₁₀               ∎
  where
  open Tools.Reasoning.PropositionalEquality
... | no _ with is-𝟘? p
... | yes _ =
  T.lam (erase s u T.[ liftSubst (T.sgSubst ↯) ]
           T.[ liftSubst (eraseSubst s σ) ])
    T.∘⟨ s ⟩ (erase s t T.[ eraseSubst s σ ])                        ≡⟨ cong (λ u → T.lam u T.∘⟨ _ ⟩ _) $
                                                                        subst-liftSubst-sgSubst (erase _ u) ⟩
  T.lam (erase s u T.[ T.liftSubstn (eraseSubst s σ) 2 ]
           T.[ liftSubst (T.sgSubst ↯) ])
    T.∘⟨ s ⟩ (erase s t T.[ eraseSubst s σ ])                        ≡⟨ cong (λ u → T.lam (u T.[ _ ]) T.∘⟨ _ ⟩ _) $
                                                                        substVar-to-subst (liftSubsts-erase-comm 2) (erase _ u) ⟩
  T.lam (erase s u T.[ eraseSubst s (U.liftSubstn σ 2) ]
           T.[ liftSubst (T.sgSubst ↯) ])
    T.∘⟨ s ⟩ (erase s t T.[ eraseSubst s σ ])                        ≡⟨ cong₂ (λ u t → T.lam (u T.[ _ ]) T.∘⟨ _ ⟩ t)
                                                                          (subst-erase-comm _ u)
                                                                          (subst-erase-comm _ t) ⟩
  T.lam (erase s (u U.[ U.liftSubstn σ 2 ])
           T.[ liftSubst (T.sgSubst ↯) ])
    T.∘⟨ s ⟩ erase s (t U.[ σ ])                                     ∎
  where
  open Tools.Reasoning.PropositionalEquality
... | no _ =
  cong₂ Term.prodrec (subst-erase-comm σ t)
        (trans (substVar-to-subst (liftSubsts-erase-comm 2) (erase _ u))
               (subst-erase-comm (U.liftSubstn σ 2) u))
subst-erase-comm σ ℕ = refl
subst-erase-comm σ U.zero = refl
subst-erase-comm {s} σ (U.suc t) =
  suc⟨ s ⟩ (erase s t) T.[ eraseSubst s σ ]  ≡⟨ suc⟨⟩-[] ⟩
  suc⟨ s ⟩ (erase s t T.[ eraseSubst s σ ])  ≡⟨ cong suc⟨ _ ⟩ (subst-erase-comm _ t) ⟩
  suc⟨ s ⟩ (erase s (t U.[ σ ]))             ∎
  where
  open Tools.Reasoning.PropositionalEquality
subst-erase-comm σ (U.natrec p q r A z s n) = cong₃ T.natrec
  (subst-erase-comm σ z)
  (trans (substVar-to-subst (liftSubsts-erase-comm 2) (erase _ s))
         (subst-erase-comm (U.liftSubst (U.liftSubst σ)) s))
  (subst-erase-comm σ n)
subst-erase-comm σ Unit! = refl
subst-erase-comm σ U.star! = refl
subst-erase-comm σ (U.unitrec p q A t u) with is-𝟘? p
... | yes _ =
  subst-erase-comm σ u
... | no _ =
  cong₂ T.unitrec (subst-erase-comm σ t)
                  (subst-erase-comm σ u)
subst-erase-comm σ Empty = refl
subst-erase-comm _ (emptyrec _ _ _) = loop-[]
subst-erase-comm _ (Id _ _ _) = refl
subst-erase-comm _ U.rfl = refl
subst-erase-comm _ (J _ _ _ _ _ u _ _) = subst-erase-comm _ u
subst-erase-comm _ (K _ _ _ _ u _) = subst-erase-comm _ u
subst-erase-comm _ ([]-cong _ _ _ _ _) = refl

subst-undefined : (x : Fin (1+ n)) →
      eraseSubst s (U.sgSubst Empty) x ≡
      T.sgSubst ↯ x
subst-undefined x0 = refl
subst-undefined (x +1) = refl

erase-consSubst-var : (σ : U.Subst m n) (a : U.Term m) (x : Fin (1+ n))
                    → T.consSubst (eraseSubst s σ) (erase s a) x
                    ≡ eraseSubst s (U.consSubst σ a) x
erase-consSubst-var σ a x0 = refl
erase-consSubst-var σ a (x +1) = refl

erase-consSubst : (σ : U.Subst m n) (a : U.Term m) (t : T.Term (1+ n))
                → t T.[ T.consSubst (eraseSubst s σ) (erase s a) ]
                ≡ t T.[ eraseSubst s (U.consSubst σ a) ]
erase-consSubst σ a t = substVar-to-subst (erase-consSubst-var σ a) t

module hasX (R : Usage-restrictions) where

  open MU R
  open MUP R
  open MUP𝟘 R

  -- Erased variables do not occur after extraction.

  erased-hasX : x ◂ 𝟘 ∈ γ → γ ▸[ 𝟙ᵐ ] t → HasX x (erase s t) → ⊥

  erased-hasX erased γ▸t@var varₓ =
    valid-var-usage γ▸t (var-usage-lookup erased)

  erased-hasX erased (lamₘ γ▸t) (lamₓ hasX) =
    erased-hasX (there erased) γ▸t hasX

  erased-hasX erased (_∘ₘ_ {γ = γ} {δ = δ} {p = p} γ▸t δ▸u) hasX
    with is-𝟘? p
  erased-hasX erased (_∘ₘ_ {γ = γ} {δ = δ} {p = p} γ▸t δ▸u) (∘ₓˡ hasX)
    | yes p≡𝟘 =
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
  erased-hasX erased (prodʷₘ {γ = γ} {p = _} {δ = δ} γ▸ _) (prodₓˡ hasX)
    | no p≢𝟘 =
    erased-hasX (x◂𝟘∈pγ refl p≢𝟘 (x◂𝟘∈γ+δˡ refl erased))
                (▸-cong (≢𝟘→⌞⌟≡𝟙ᵐ p≢𝟘) γ▸) hasX
  erased-hasX erased (prodʷₘ {γ = γ} {p = _} {δ = δ} _ δ▸) (prodₓʳ hasX)
    | no _ =
    erased-hasX (x◂𝟘∈γ+δʳ refl erased) δ▸ hasX

  erased-hasX erased (prodˢₘ {γ = γ} {p = p} {δ = δ} _ γ▸u) hasX
    with is-𝟘? p
  ... | yes refl = erased-hasX (x◂𝟘∈γ∧δʳ refl erased) γ▸u hasX
  erased-hasX erased (prodˢₘ {γ = γ} {p = p} {δ = δ} γ▸ _) (prodₓˡ hasX)
    | no p≢𝟘 =
    erased-hasX (x◂𝟘∈pγ refl p≢𝟘 (x◂𝟘∈γ∧δˡ refl erased))
                (▸-cong (≢𝟘→⌞⌟≡𝟙ᵐ p≢𝟘) γ▸) hasX
  erased-hasX erased (prodˢₘ {γ = γ} {p = _} {δ = δ} _ δ▸) (prodₓʳ hasX)
    | no p≢𝟘 =
    erased-hasX erased (sub δ▸ (∧ᶜ-decreasingʳ _ _)) hasX

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
      (HasX-[closed,closed]→ (λ ()) (λ ()) hasX)
  ... | no _ with is-𝟘? p
  erased-hasX erased (prodrecₘ {u} _ ▸u _ _) (∘ₓˡ (lamₓ hasX))
    | no _ | yes _ =
    case HasX-[liftSubst]→ {t = erase _ u} hasX of λ where
      (inj₁ (() , _))
      (inj₂ (_ , refl , x0     , _    , ()))
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
  erased-hasX erased (natrecₘ _ δ▸s _ _) (natrecₓˢ hasX) =
    erased-hasX (there (there (◂𝟘∈nrᶜ₂ refl erased))) δ▸s hasX
  erased-hasX erased
    (natrec-no-nrₘ _ δ▸s _ _ _ _ _ fix)
    (natrecₓˢ hasX) =
    erased-hasX
      (there $ there $ x◂𝟘∈γ+δˡ refl $ x◂𝟘∈γ≤δ erased fix)
      δ▸s hasX
  erased-hasX erased (natrecₘ _ _ η▸n _) (natrecₓⁿ hasX) =
    erased-hasX (◂𝟘∈nrᶜ₃ refl erased) η▸n hasX
  erased-hasX erased
    (natrec-no-nrₘ _ _ η▸n _ _ _ χ≤η _)
    (natrecₓⁿ hasX) =
    erased-hasX (x◂𝟘∈γ≤δ erased χ≤η) η▸n hasX

  erased-hasX erased (Jₘ _ _ _ _ _ ▸u _ _) hasX =
    erased-hasX
      (x◂𝟘∈γ∧δˡ refl $ x◂𝟘∈γ∧δʳ refl $ x◂𝟘∈γ∧δʳ refl $
       x◂𝟘∈pγ refl ω≢𝟘 erased)
      ▸u hasX
  erased-hasX erased (J₀ₘ₁ _ _ _ _ _ _ ▸u _ _) hasX =
    erased-hasX (x◂𝟘∈γ∧δʳ refl $ x◂𝟘∈pγ refl ω≢𝟘 erased) ▸u hasX
  erased-hasX erased (J₀ₘ₂ _ _ _ _ ▸u _ _) hasX =
    erased-hasX erased ▸u hasX
  erased-hasX erased (Kₘ _ _ _ _ _ ▸u _) hasX =
    erased-hasX
      (x◂𝟘∈γ∧δˡ refl $ x◂𝟘∈γ∧δʳ refl $ x◂𝟘∈γ∧δʳ refl $
       x◂𝟘∈pγ refl ω≢𝟘 erased)
      ▸u hasX
  erased-hasX erased (K₀ₘ₁ _ _ _ _ _ ▸u _) hasX =
    erased-hasX (x◂𝟘∈γ∧δʳ refl $ x◂𝟘∈pγ refl ω≢𝟘 erased) ▸u hasX
  erased-hasX erased (K₀ₘ₂ _ _ _ _ ▸u _) hasX =
    erased-hasX erased ▸u hasX

  erased-hasX erased (unitrecₘ {p = p} γ▸t δ▸u η▸A ok) hasX
    with is-𝟘? p
  erased-hasX erased (unitrecₘ _ δ▸u _ _) hasX | yes _ =
    erased-hasX (x◂𝟘∈γ+δʳ refl erased) δ▸u hasX
  erased-hasX erased (unitrecₘ {p = _} γ▸t δ▸u η▸A ok) (unitrecₓˡ hasX) | no p≢𝟘 =
    erased-hasX (x◂𝟘∈pγ refl p≢𝟘 (x◂𝟘∈γ+δˡ refl erased))
                (▸-cong (≢𝟘→⌞⌟≡𝟙ᵐ p≢𝟘) γ▸t) hasX
  erased-hasX erased (unitrecₘ {p = _} γ▸t δ▸u η▸A ok) (unitrecₓʳ hasX) | no _ =
    erased-hasX (x◂𝟘∈γ+δʳ refl erased) δ▸u hasX

  erased-hasX _ (emptyrecₘ _ _) =
    loop-closed

  erased-hasX erased (sub δ▸t γ≤δ) hasX =
    erased-hasX (x◂𝟘∈γ≤δ erased γ≤δ) δ▸t hasX

  -- Agda might type-check the proof a little quicker if the following
  -- cases are included.
  erased-hasX _ Uₘ                 ()
  erased-hasX _ ℕₘ                 ()
  erased-hasX _ Emptyₘ             ()
  erased-hasX _ Unitₘ              ()
  erased-hasX _ (ΠΣₘ _ _)          ()
  erased-hasX _ (Idₘ _ _ _ _)      ()
  erased-hasX _ (Id₀ₘ _ _ _ _)     ()
  erased-hasX _ starʷₘ             ()
  erased-hasX _ (starˢₘ _)         ()
  erased-hasX _ rflₘ               ()
  erased-hasX _ ([]-congₘ _ _ _ _) ()
