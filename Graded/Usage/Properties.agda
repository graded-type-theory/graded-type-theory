------------------------------------------------------------------------
-- Properties of the usage relation.
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

import Graded.Modality
open import Graded.Usage.Restrictions

module Graded.Usage.Properties
  {a} {M : Set a}
  (open Graded.Modality M)
  (𝕄 : Modality)
  (R : Usage-restrictions 𝕄)
  where

open Modality 𝕄
open Usage-restrictions R

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Usage 𝕄 R
open import Graded.Usage.Inversion 𝕄 R
open import Graded.Modality.Dedicated-nr 𝕄
open import Graded.Modality.Nr-instances
open import Graded.Modality.Properties 𝕄
open import Graded.Mode 𝕄

import Definition.Typed
open import Definition.Typed.Restrictions 𝕄
open import Definition.Untyped M hiding (_∷_)

open import Tools.Bool using (Bool; T)
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Level
open import Tools.Nat using (Nat; 1+)
open import Tools.Product
open import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Sum
open import Tools.Unit
import Tools.Reasoning.Equivalence
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality

private
  variable
    n : Nat
    Γ : Con Term n
    A B F t u v w : Term n
    G : Term (1+ n)
    γ γ₁ γ₂ γ₃ γ₄ γ₅ γ₆ δ η θ χ : Conₘ n
    p q r s z : M
    m m₁ m₂ m′ : Mode
    bm : BinderMode
    str : Strength
    b : Bool
    ok : T b
    x : Fin n

------------------------------------------------------------------------
-- Lemmas related to _◂_∈_

-- Variables only have one annotation in a context

unique-var-usage : x ◂ p ∈ γ → x ◂ q ∈ γ → p PE.≡ q
unique-var-usage here here = PE.refl
unique-var-usage (there x) (there y) = unique-var-usage x y

-- Variable lookup and the usage relation for variables match

var-usage-lookup : x ◂ p ∈ γ → γ ⟨ x ⟩ ≡ p
var-usage-lookup here = PE.refl
var-usage-lookup (there x) = var-usage-lookup x

-- An alternative characterisation of _◂_∈_.

◂∈⇔ : x ◂ p ∈ γ ⇔ γ ⟨ x ⟩ ≡ p
◂∈⇔ = to , from
  where
  to : x ◂ p ∈ γ → γ ⟨ x ⟩ ≡ p
  to here      = refl
  to (there q) = to q

  from : γ ⟨ x ⟩ ≡ p → x ◂ p ∈ γ
  from {γ = _ ∙ _} {x = x0}   refl = here
  from {γ = _ ∙ _} {x = _ +1} eq   = there (from eq)

------------------------------------------------------------------------
-- Replacing one usage mode with another

-- γ ▸[_] t respects _≡_.

▸-cong : m₁ ≡ m₂ → γ ▸[ m₁ ] t → γ ▸[ m₂ ] t
▸-cong = subst (_ ▸[_] _)

-- If 𝟘ᵐ is not allowed, then one can convert usage modes freely.

▸-without-𝟘ᵐ : ¬ T 𝟘ᵐ-allowed → γ ▸[ m ] t → γ ▸[ m′ ] t
▸-without-𝟘ᵐ not-ok =
  ▸-cong (Mode-propositional-without-𝟘ᵐ not-ok)

-- If the modality is trivial, then one can convert usage modes
-- freely.

▸-trivial : Trivial → γ ▸[ m ] t → γ ▸[ m′ ] t
▸-trivial 𝟙≡𝟘 = ▸-without-𝟘ᵐ (flip 𝟘ᵐ.non-trivial 𝟙≡𝟘)

------------------------------------------------------------------------
-- The lemma ▸-· and some related results

-- The relation _▸[_]_ respects multiplication (in a certain sense).

▸-· : γ ▸[ m ] t → ⌜ m′ ⌝ ·ᶜ γ ▸[ m′ ·ᵐ m ] t

-- If a term is well-resourced with respect to any context and mode,
-- then it is well-resourced with respect to the zero usage context
-- and the mode 𝟘ᵐ[ ok ].

▸-𝟘 : γ ▸[ m ] t → 𝟘ᶜ ▸[ 𝟘ᵐ[ ok ] ] t
▸-𝟘 {γ} ▸t = sub
  (▸-· ▸t)
  (begin
     𝟘ᶜ      ≈˘⟨ ·ᶜ-zeroˡ _ ⟩
     𝟘 ·ᶜ γ  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- If a term is well-resourced with respect to any context and mode,
-- then it is well-resourced with respect to some usage context and
-- the mode 𝟘ᵐ?.

▸-𝟘ᵐ? : γ ▸[ m ] t → ∃ λ δ → δ ▸[ 𝟘ᵐ? ] t
▸-𝟘ᵐ? {m = 𝟘ᵐ[ ok ]} ▸t =
  _ , ▸-cong (PE.sym $ 𝟘ᵐ?≡𝟘ᵐ {ok = ok}) (▸-𝟘 ▸t)
▸-𝟘ᵐ? {m = 𝟙ᵐ} {t} ▸t = 𝟘ᵐ?-elim
  (λ m → ∃ λ δ → δ ▸[ m ] t)
  (_ , ▸-𝟘 ▸t)
  (λ _ → _ , ▸t)

▸-· Uₘ =
  sub Uₘ (≤ᶜ-reflexive (·ᶜ-zeroʳ _))
▸-· ℕₘ =
  sub ℕₘ (≤ᶜ-reflexive (·ᶜ-zeroʳ _))
▸-· Emptyₘ =
  sub Emptyₘ (≤ᶜ-reflexive (·ᶜ-zeroʳ _))
▸-· Unitₘ =
  sub Unitₘ (≤ᶜ-reflexive (·ᶜ-zeroʳ _))
▸-· {m′ = m′} (ΠΣₘ F G) = sub
  (ΠΣₘ (▸-cong (PE.sym (·ᵐ-ᵐ·-assoc m′)) (▸-· F))
       (sub (▸-· G) (≤ᶜ-reflexive (≈ᶜ-refl ∙ ·ᵐ-·-assoc m′))))
  (≤ᶜ-reflexive (·ᶜ-distribˡ-+ᶜ _ _ _))
▸-· {m = m} {m′ = m′} (var {x = x}) = sub var
  (begin
     ⌜ m′ ⌝ ·ᶜ (𝟘ᶜ , x ≔ ⌜ m ⌝)    ≡˘⟨ update-distrib-·ᶜ _ _ _ _ ⟩
     ⌜ m′ ⌝ ·ᶜ 𝟘ᶜ , x ≔ ⌜ m′ ⌝ · ⌜ m ⌝  ≈⟨ update-congˡ (·ᶜ-zeroʳ _) ⟩
     𝟘ᶜ , x ≔ ⌜ m′ ⌝ · ⌜ m ⌝            ≈˘⟨ update-congʳ (⌜·ᵐ⌝ m′) ⟩
     𝟘ᶜ , x ≔ ⌜ m′ ·ᵐ m ⌝               ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
▸-· {m′ = m′} (lamₘ t) = lamₘ
  (sub (▸-· t) (≤ᶜ-reflexive (≈ᶜ-refl ∙ ·ᵐ-·-assoc m′)))
▸-· {m′ = m′} (_∘ₘ_ {γ = γ} {δ = δ} {p = p} t u) = sub
  (▸-· t ∘ₘ ▸-cong (PE.sym (·ᵐ-ᵐ·-assoc m′)) (▸-· u))
  (begin
     ⌜ m′ ⌝ ·ᶜ (γ +ᶜ p ·ᶜ δ)          ≈⟨ ·ᶜ-distribˡ-+ᶜ _ _ _ ⟩
     ⌜ m′ ⌝ ·ᶜ γ +ᶜ ⌜ m′ ⌝ ·ᶜ p ·ᶜ δ  ≈⟨ +ᶜ-congˡ
                                           (≈ᶜ-trans (≈ᶜ-sym (·ᶜ-assoc _ _ _))
                                              (≈ᶜ-trans (·ᶜ-congʳ (⌜⌝-·-comm m′))
                                                 (·ᶜ-assoc _ _ _))) ⟩
     ⌜ m′ ⌝ ·ᶜ γ +ᶜ p ·ᶜ ⌜ m′ ⌝ ·ᶜ δ  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
▸-· {m′ = m′} (prodʷₘ {γ = γ} {p = p} {δ = δ} t u) = sub
  (prodʷₘ (▸-cong (PE.sym (·ᵐ-ᵐ·-assoc m′)) (▸-· t)) (▸-· u))
  (begin
     ⌜ m′ ⌝ ·ᶜ (p ·ᶜ γ +ᶜ δ)           ≈⟨ ·ᶜ-distribˡ-+ᶜ _ _ _ ⟩
     ⌜ m′ ⌝ ·ᶜ p ·ᶜ γ +ᶜ ⌜ m′ ⌝ ·ᶜ δ   ≈˘⟨ +ᶜ-congʳ (·ᶜ-assoc _ _ _) ⟩
     (⌜ m′ ⌝ · p) ·ᶜ γ +ᶜ ⌜ m′ ⌝ ·ᶜ δ  ≈⟨ +ᶜ-congʳ (·ᶜ-congʳ (⌜⌝-·-comm m′)) ⟩
     (p · ⌜ m′ ⌝) ·ᶜ γ +ᶜ ⌜ m′ ⌝ ·ᶜ δ  ≈⟨ +ᶜ-congʳ (·ᶜ-assoc _ _ _) ⟩
     p ·ᶜ ⌜ m′ ⌝ ·ᶜ γ +ᶜ ⌜ m′ ⌝ ·ᶜ δ   ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
▸-· {m′ = m′} (prodˢₘ {γ = γ} {m = m} {p = p} {δ = δ} t u) = sub
  (prodˢₘ (▸-cong (PE.sym (·ᵐ-ᵐ·-assoc m′)) (▸-· t)) (▸-· u))
  (begin
     ⌜ m′ ⌝ ·ᶜ (p ·ᶜ γ ∧ᶜ δ)           ≈⟨ ·ᶜ-distribˡ-∧ᶜ _ _ _ ⟩
     ⌜ m′ ⌝ ·ᶜ p ·ᶜ γ ∧ᶜ ⌜ m′ ⌝ ·ᶜ δ   ≈˘⟨ ∧ᶜ-congʳ (·ᶜ-assoc _ _ _) ⟩
     (⌜ m′ ⌝ · p) ·ᶜ γ ∧ᶜ ⌜ m′ ⌝ ·ᶜ δ  ≈⟨ ∧ᶜ-congʳ (·ᶜ-congʳ (⌜⌝-·-comm m′)) ⟩
     (p · ⌜ m′ ⌝) ·ᶜ γ ∧ᶜ ⌜ m′ ⌝ ·ᶜ δ  ≈⟨ ∧ᶜ-congʳ (·ᶜ-assoc _ _ _) ⟩
     p ·ᶜ ⌜ m′ ⌝ ·ᶜ γ ∧ᶜ ⌜ m′ ⌝ ·ᶜ δ   ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
▸-· {m′ = m′} (fstₘ m t PE.refl ok) = fstₘ
  (m′ ·ᵐ m)
  (▸-cong (PE.sym (·ᵐ-ᵐ·-assoc m′)) (▸-· t))
  (·ᵐ-ᵐ·-assoc m′)
  λ m′·m≡𝟙 → ok (·ᵐ-𝟙ʳ m′·m≡𝟙)
▸-· (sndₘ t) =
  sndₘ (▸-· t)
▸-· {m′ = m′} (prodrecₘ {γ = γ} {m = m} {r = r} {δ = δ} t u A ok) = sub
  (prodrecₘ
     (▸-cong (PE.sym (·ᵐ-ᵐ·-assoc m′)) (▸-· t))
     (sub (▸-· u)
        (≤ᶜ-reflexive (≈ᶜ-refl ∙ ·ᵐ-·-assoc m′ ∙ ·ᵐ-·-assoc m′)))
     A
     (Prodrec-allowed-·ᵐ ok))
  (begin
     ⌜ m′ ⌝ ·ᶜ (r ·ᶜ γ +ᶜ δ)          ≈⟨ ·ᶜ-distribˡ-+ᶜ _ _ _ ⟩
     ⌜ m′ ⌝ ·ᶜ r ·ᶜ γ +ᶜ ⌜ m′ ⌝ ·ᶜ δ  ≈⟨ +ᶜ-congʳ
                                           (≈ᶜ-trans (≈ᶜ-sym (·ᶜ-assoc _ _ _))
                                              (≈ᶜ-trans (·ᶜ-congʳ (⌜⌝-·-comm m′))
                                                 (·ᶜ-assoc _ _ _))) ⟩
     r ·ᶜ ⌜ m′ ⌝ ·ᶜ γ +ᶜ ⌜ m′ ⌝ ·ᶜ δ  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
▸-· zeroₘ =
  sub zeroₘ (≤ᶜ-reflexive (·ᶜ-zeroʳ _))
▸-· (sucₘ t) =
  sucₘ (▸-· t)
▸-· {m = m} {m′ = m′}
  (natrecₘ {γ = γ} {δ = δ} {p = p} {r = r} {η = η}
     γ▸z δ▸s η▸n θ▸A) = sub
  (natrecₘ (▸-· γ▸z)
     (sub (▸-· δ▸s)
        (≤ᶜ-reflexive (≈ᶜ-refl ∙ ·ᵐ-·-assoc m′ ∙ ·ᵐ-·-assoc m′)))
     (▸-· η▸n)
     θ▸A)
  (begin
     ⌜ m′ ⌝ ·ᶜ nrᶜ p r γ δ η                            ≈⟨ ⌜⌝ᶜ-·ᶜ-distribˡ-nrᶜ m′ ⟩
     nrᶜ p r (⌜ m′ ⌝ ·ᶜ γ) (⌜ m′ ⌝ ·ᶜ δ) (⌜ m′ ⌝ ·ᶜ η)  ∎)
  where
  open import Graded.Modality.Dedicated-nr.Instance
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
▸-· {m = m} {m′ = m′}
  (natrec-no-nrₘ {γ = γ} {δ = δ} {p = p} {r = r} {η = η} {χ = χ}
     γ▸z δ▸s η▸n θ▸A χ≤γ χ≤δ χ≤η fix) =
  natrec-no-nrₘ (▸-· γ▸z)
    (sub (▸-· δ▸s)
       (≤ᶜ-reflexive (≈ᶜ-refl ∙ ·ᵐ-·-assoc m′ ∙ ·ᵐ-·-assoc m′)))
    (▸-· η▸n)
    θ▸A
    (begin
       ⌜ m′ ⌝ ·ᶜ χ  ≤⟨ ·ᶜ-monotoneʳ χ≤γ ⟩
       ⌜ m′ ⌝ ·ᶜ γ  ∎)
    (λ ok → begin
       ⌜ m′ ⌝ ·ᶜ χ  ≤⟨ ·ᶜ-monotoneʳ (χ≤δ ok) ⟩
       ⌜ m′ ⌝ ·ᶜ δ  ∎)
    (begin
       ⌜ m′ ⌝ ·ᶜ χ  ≤⟨ ·ᶜ-monotoneʳ χ≤η ⟩
       ⌜ m′ ⌝ ·ᶜ η  ∎)
    (begin
       ⌜ m′ ⌝ ·ᶜ χ                                          ≤⟨ ·ᶜ-monotoneʳ fix ⟩

       ⌜ m′ ⌝ ·ᶜ (δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ χ)                    ≈⟨ ≈ᶜ-trans (·ᶜ-distribˡ-+ᶜ _ _ _) $
                                                               +ᶜ-congˡ $
                                                               ·ᶜ-distribˡ-+ᶜ _ _ _ ⟩
       ⌜ m′ ⌝ ·ᶜ δ +ᶜ ⌜ m′ ⌝ ·ᶜ p ·ᶜ η +ᶜ ⌜ m′ ⌝ ·ᶜ r ·ᶜ χ  ≈⟨ +ᶜ-congˡ $ +ᶜ-cong
                                                               (≈ᶜ-trans (≈ᶜ-sym (·ᶜ-assoc _ _ _)) $
                                                                ≈ᶜ-trans (·ᶜ-congʳ (⌜⌝-·-comm m′)) $
                                                                ·ᶜ-assoc _ _ _)
                                                               (≈ᶜ-trans (≈ᶜ-sym (·ᶜ-assoc _ _ _)) $
                                                                ≈ᶜ-trans (·ᶜ-congʳ (⌜⌝-·-comm m′)) $
                                                                ·ᶜ-assoc _ _ _) ⟩
       ⌜ m′ ⌝ ·ᶜ δ +ᶜ p ·ᶜ ⌜ m′ ⌝ ·ᶜ η +ᶜ r ·ᶜ ⌜ m′ ⌝ ·ᶜ χ  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
▸-· {m′ = m′} (emptyrecₘ {γ = γ} {m = m} {p = p} e A) = sub
  (emptyrecₘ (▸-cong (PE.sym (·ᵐ-ᵐ·-assoc m′)) (▸-· e)) A)
  (begin
     ⌜ m′ ⌝ ·ᶜ p ·ᶜ γ   ≈˘⟨ ·ᶜ-assoc _ _ _ ⟩
     (⌜ m′ ⌝ · p) ·ᶜ γ  ≈⟨ ·ᶜ-congʳ (⌜⌝-·-comm m′) ⟩
     (p · ⌜ m′ ⌝) ·ᶜ γ  ≈⟨ ·ᶜ-assoc _ _ _ ⟩
     p ·ᶜ ⌜ m′ ⌝ ·ᶜ γ   ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
▸-· starʷₘ = sub starʷₘ (≤ᶜ-reflexive (·ᶜ-zeroʳ _))
▸-· {m′ = m′} (starˢₘ prop) =
  sub (starˢₘ prop) (≤ᶜ-reflexive (≈ᶜ-sym (·ᵐ-·ᶜ-assoc m′)))
▸-· {m′ = m′} (unitrecₘ {γ = γ} {p = p} {δ = δ} γ▸t δ▸u η▸A ok) = sub
  (unitrecₘ (▸-cong (PE.sym (·ᵐ-ᵐ·-assoc m′)) (▸-· γ▸t)) (▸-· δ▸u) η▸A
     (Unitrec-allowed-·ᵐ ok))
  (begin
    ⌜ m′ ⌝ ·ᶜ (p ·ᶜ γ +ᶜ δ)           ≈⟨ ·ᶜ-distribˡ-+ᶜ _ _ _ ⟩
    ⌜ m′ ⌝ ·ᶜ p ·ᶜ γ +ᶜ ⌜ m′ ⌝ ·ᶜ δ   ≈˘⟨ +ᶜ-congʳ (·ᶜ-assoc _ _ _) ⟩
    (⌜ m′ ⌝ · p) ·ᶜ γ +ᶜ ⌜ m′ ⌝ ·ᶜ δ  ≈⟨ +ᶜ-congʳ (·ᶜ-congʳ (⌜⌝-·-comm m′)) ⟩
    (p · ⌜ m′ ⌝) ·ᶜ γ +ᶜ ⌜ m′ ⌝ ·ᶜ δ  ≈⟨ +ᶜ-congʳ (·ᶜ-assoc _ _ _) ⟩
    p ·ᶜ ⌜ m′ ⌝ ·ᶜ γ +ᶜ ⌜ m′ ⌝ ·ᶜ δ   ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
▸-· (Idₘ ok ▸A ▸t ▸u) = sub
  (Idₘ ok ▸A (▸-· ▸t) (▸-· ▸u))
  (≤ᶜ-reflexive (·ᶜ-distribˡ-+ᶜ _ _ _))
▸-· (Id₀ₘ ok ▸A ▸t ▸u) = sub
  (Id₀ₘ ok ▸A ▸t ▸u)
  (≤ᶜ-reflexive (·ᶜ-zeroʳ _))
▸-· rflₘ =
  sub rflₘ (≤ᶜ-reflexive (·ᶜ-zeroʳ _))
▸-· {m} {m′}
  (Jₘ {γ₂} {γ₃} {p} {q} {B} {γ₄} {γ₅} {γ₆} _ ▸A ▸t ▸B ▸u ▸v ▸w) =
  case Erased-matches-for-J? (m′ ·ᵐ m) of λ where
    (no ok) → sub
      (Jₘ ok ▸A (▸-· ▸t)
         (sub (▸-· ▸B)
            (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
               ⌜ m′ ⌝ ·ᶜ γ₃ ∙ ⌜ m′ ·ᵐ m ⌝ · p ∙ ⌜ m′ ·ᵐ m ⌝ · q            ≈⟨ ≈ᶜ-refl ∙ ·-congʳ (⌜·ᵐ⌝ m′) ∙ ·-congʳ (⌜·ᵐ⌝ m′) ⟩
               ⌜ m′ ⌝ ·ᶜ γ₃ ∙ (⌜ m′ ⌝ · ⌜ m ⌝) · p ∙ (⌜ m′ ⌝ · ⌜ m ⌝) · q  ≈⟨ ≈ᶜ-refl ∙ ·-assoc _ _ _ ∙ ·-assoc _ _ _ ⟩
               ⌜ m′ ⌝ ·ᶜ γ₃ ∙ ⌜ m′ ⌝ · ⌜ m ⌝ · p ∙ ⌜ m′ ⌝ · ⌜ m ⌝ · q      ∎))
         (▸-· ▸u) (▸-· ▸v) (▸-· ▸w))
      (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
         ⌜ m′ ⌝ ·ᶜ ω ·ᶜ (γ₂ ∧ᶜ γ₃ ∧ᶜ γ₄ ∧ᶜ γ₅ ∧ᶜ γ₆)                       ≈⟨ ≈ᶜ-trans (≈ᶜ-sym (·ᶜ-assoc _ _ _)) $
                                                                              ≈ᶜ-trans (·ᶜ-congʳ (⌜⌝-·-comm m′)) $
                                                                              ·ᶜ-assoc _ _ _ ⟩

         ω ·ᶜ ⌜ m′ ⌝ ·ᶜ (γ₂ ∧ᶜ γ₃ ∧ᶜ γ₄ ∧ᶜ γ₅ ∧ᶜ γ₆)                       ≈⟨ ·ᶜ-congˡ $
                                                                              ≈ᶜ-trans (·ᶜ-distribˡ-∧ᶜ _ _ _) $ ∧ᶜ-congˡ $
                                                                              ≈ᶜ-trans (·ᶜ-distribˡ-∧ᶜ _ _ _) $ ∧ᶜ-congˡ $
                                                                              ≈ᶜ-trans (·ᶜ-distribˡ-∧ᶜ _ _ _) $ ∧ᶜ-congˡ $
                                                                              ·ᶜ-distribˡ-∧ᶜ _ _ _ ⟩
         ω ·ᶜ
         (⌜ m′ ⌝ ·ᶜ γ₂ ∧ᶜ ⌜ m′ ⌝ ·ᶜ γ₃ ∧ᶜ ⌜ m′ ⌝ ·ᶜ γ₄ ∧ᶜ ⌜ m′ ⌝ ·ᶜ γ₅ ∧ᶜ
          ⌜ m′ ⌝ ·ᶜ γ₆)                                                    ∎)
    (yes ok) → sub
      (J₀ₘ ok ▸A (▸-𝟘ᵐ? ▸t .proj₂)
         (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
          𝟘ᵐ?-elim (λ m′ → ∃ λ δ → δ ∙ ⌜ m′ ⌝ · p ∙ ⌜ m′ ⌝ · q ▸[ m′ ] B)
            ( 𝟘ᶜ
            , sub (▸-𝟘 ▸B) (begin
                𝟘ᶜ ∙ 𝟘 · p ∙ 𝟘 · q  ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ∙ ·-zeroˡ _ ⟩
                𝟘ᶜ                  ∎)
            )
            (λ not-ok →
                 γ₃
               , sub (▸-cong (only-𝟙ᵐ-without-𝟘ᵐ not-ok) ▸B) (begin
                   γ₃ ∙ 𝟙 · p ∙ 𝟙 · q          ≈⟨ ≈ᶜ-refl ∙
                                                  cong (λ m → ⌜ m ⌝ · p) (Mode-propositional-without-𝟘ᵐ {m₁ = 𝟙ᵐ} {m₂ = m} not-ok) ∙
                                                  cong (λ m → ⌜ m ⌝ · q) (Mode-propositional-without-𝟘ᵐ {m₁ = 𝟙ᵐ} {m₂ = m} not-ok) ⟩
                   γ₃ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · q  ∎))
            .proj₂)
         (▸-· ▸u) (▸-𝟘ᵐ? ▸v .proj₂) (▸-𝟘ᵐ? ▸w .proj₂))
      (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
         ⌜ m′ ⌝ ·ᶜ ω ·ᶜ (γ₂ ∧ᶜ γ₃ ∧ᶜ γ₄ ∧ᶜ γ₅ ∧ᶜ γ₆)      ≤⟨ ·ᶜ-monotoneʳ ω·ᶜ-decreasing ⟩

         ⌜ m′ ⌝ ·ᶜ (γ₂ ∧ᶜ γ₃ ∧ᶜ γ₄ ∧ᶜ γ₅ ∧ᶜ γ₆)           ≈⟨ ≈ᶜ-trans (·ᶜ-distribˡ-∧ᶜ _ _ _) $ ∧ᶜ-congˡ $
                                                             ≈ᶜ-trans (·ᶜ-distribˡ-∧ᶜ _ _ _) $ ∧ᶜ-congˡ $
                                                             ·ᶜ-distribˡ-∧ᶜ _ _ _ ⟩
         ⌜ m′ ⌝ ·ᶜ γ₂ ∧ᶜ ⌜ m′ ⌝ ·ᶜ γ₃ ∧ᶜ ⌜ m′ ⌝ ·ᶜ γ₄ ∧ᶜ
         ⌜ m′ ⌝ ·ᶜ (γ₅ ∧ᶜ γ₆)                             ≤⟨ ≤ᶜ-trans (∧ᶜ-decreasingʳ _ _) $
                                                             ≤ᶜ-trans (∧ᶜ-decreasingʳ _ _) $
                                                             ∧ᶜ-decreasingˡ _ _ ⟩
         ⌜ m′ ⌝ ·ᶜ γ₄                                     ∎)
▸-· (J₀ₘ ok ▸A ▸t ▸F ▸u ▸v ▸w) =
  J₀ₘ (Erased-matches-for-J-·ᵐ ok) ▸A ▸t ▸F (▸-· ▸u) ▸v ▸w
▸-· {m} {m′} (Kₘ {γ₂} {γ₃} {p} {B} {γ₄} {γ₅} _ ▸A ▸t ▸B ▸u ▸v) =
  case Erased-matches-for-K? (m′ ·ᵐ m) of λ where
    (no ok) → sub
      (Kₘ ok ▸A (▸-· ▸t)
         (sub (▸-· ▸B)
            (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
               ⌜ m′ ⌝ ·ᶜ γ₃ ∙ ⌜ m′ ·ᵐ m ⌝ · p       ≈⟨ ≈ᶜ-refl ∙ ·-congʳ (⌜·ᵐ⌝ m′) ⟩
               ⌜ m′ ⌝ ·ᶜ γ₃ ∙ (⌜ m′ ⌝ · ⌜ m ⌝) · p  ≈⟨ ≈ᶜ-refl ∙ ·-assoc _ _ _ ⟩
               ⌜ m′ ⌝ ·ᶜ γ₃ ∙ ⌜ m′ ⌝ · ⌜ m ⌝ · p    ∎))
         (▸-· ▸u) (▸-· ▸v))
      (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
         ⌜ m′ ⌝ ·ᶜ ω ·ᶜ (γ₂ ∧ᶜ γ₃ ∧ᶜ γ₄ ∧ᶜ γ₅)                           ≈⟨ ≈ᶜ-trans (≈ᶜ-sym (·ᶜ-assoc _ _ _)) $
                                                                            ≈ᶜ-trans (·ᶜ-congʳ (⌜⌝-·-comm m′)) $
                                                                            ·ᶜ-assoc _ _ _ ⟩

         ω ·ᶜ ⌜ m′ ⌝ ·ᶜ (γ₂ ∧ᶜ γ₃ ∧ᶜ γ₄ ∧ᶜ γ₅)                           ≈⟨ ·ᶜ-congˡ $
                                                                            ≈ᶜ-trans (·ᶜ-distribˡ-∧ᶜ _ _ _) $ ∧ᶜ-congˡ $
                                                                            ≈ᶜ-trans (·ᶜ-distribˡ-∧ᶜ _ _ _) $ ∧ᶜ-congˡ $
                                                                            ·ᶜ-distribˡ-∧ᶜ _ _ _ ⟩
         ω ·ᶜ
         (⌜ m′ ⌝ ·ᶜ γ₂ ∧ᶜ ⌜ m′ ⌝ ·ᶜ γ₃ ∧ᶜ ⌜ m′ ⌝ ·ᶜ γ₄ ∧ᶜ ⌜ m′ ⌝ ·ᶜ γ₅)  ∎)
    (yes ok) → sub
      (K₀ₘ ok ▸A (▸-𝟘ᵐ? ▸t .proj₂)
         (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
          𝟘ᵐ?-elim (λ m′ → ∃ λ δ → δ ∙ ⌜ m′ ⌝ · p ▸[ m′ ] B)
            ( 𝟘ᶜ
            , sub (▸-𝟘 ▸B) (begin
                𝟘ᶜ ∙ 𝟘 · p  ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
                𝟘ᶜ          ∎)
            )
            (λ not-ok →
                 γ₃
               , sub (▸-cong (only-𝟙ᵐ-without-𝟘ᵐ not-ok) ▸B) (begin
                   γ₃ ∙ 𝟙 · p      ≈⟨ ≈ᶜ-refl ∙
                                      cong (λ m → ⌜ m ⌝ · p) (Mode-propositional-without-𝟘ᵐ {m₁ = 𝟙ᵐ} {m₂ = m} not-ok) ⟩
                   γ₃ ∙ ⌜ m ⌝ · p  ∎))
            .proj₂)
         (▸-· ▸u) (▸-𝟘ᵐ? ▸v .proj₂))
      (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
         ⌜ m′ ⌝ ·ᶜ ω ·ᶜ (γ₂ ∧ᶜ γ₃ ∧ᶜ γ₄ ∧ᶜ γ₅)                         ≤⟨ ·ᶜ-monotoneʳ ω·ᶜ-decreasing ⟩

         ⌜ m′ ⌝ ·ᶜ (γ₂ ∧ᶜ γ₃ ∧ᶜ γ₄ ∧ᶜ γ₅)                              ≈⟨ ≈ᶜ-trans (·ᶜ-distribˡ-∧ᶜ _ _ _) $ ∧ᶜ-congˡ $
                                                                          ≈ᶜ-trans (·ᶜ-distribˡ-∧ᶜ _ _ _) $ ∧ᶜ-congˡ $
                                                                          ·ᶜ-distribˡ-∧ᶜ _ _ _ ⟩
         ⌜ m′ ⌝ ·ᶜ γ₂ ∧ᶜ ⌜ m′ ⌝ ·ᶜ γ₃ ∧ᶜ ⌜ m′ ⌝ ·ᶜ γ₄ ∧ᶜ ⌜ m′ ⌝ ·ᶜ γ₅  ≤⟨ ≤ᶜ-trans (∧ᶜ-decreasingʳ _ _) $
                                                                          ≤ᶜ-trans (∧ᶜ-decreasingʳ _ _) $
                                                                          ∧ᶜ-decreasingˡ _ _ ⟩
         ⌜ m′ ⌝ ·ᶜ γ₄                                                  ∎)
▸-· (K₀ₘ ok ▸A ▸t ▸F ▸u ▸v) =
  K₀ₘ (Erased-matches-for-K-·ᵐ ok) ▸A ▸t ▸F (▸-· ▸u) ▸v
▸-· ([]-congₘ ▸A ▸t ▸u ▸v) = sub
  ([]-congₘ ▸A ▸t ▸u ▸v)
  (≤ᶜ-reflexive (·ᶜ-zeroʳ _))
▸-· (sub γ▸t δ≤γ) =
  sub (▸-· γ▸t) (·ᶜ-monotoneʳ δ≤γ)

-- The relation _▸[_]_ respects multiplication (in a certain sense).

▸-·′ : γ ▸[ m ] t → ⌜ m ⌝ ·ᶜ γ ▸[ m ] t
▸-·′ ▸t = ▸-cong ·ᵐ-idem (▸-· ▸t)

opaque

  -- A variant of ▸-𝟘.

  𝟘ᶜ▸[𝟘ᵐ?] : T 𝟘ᵐ-allowed → γ ▸[ m ] t → 𝟘ᶜ ▸[ 𝟘ᵐ? ] t
  𝟘ᶜ▸[𝟘ᵐ?] ok = ▸-cong (PE.sym $ 𝟘ᵐ?≡𝟘ᵐ {ok = ok}) ∘→ ▸-𝟘

-- If a term does not use any resources, then it is well-resourced
-- with respect to any mode.

𝟘ᶜ▸[𝟙ᵐ]→ : 𝟘ᶜ ▸[ 𝟙ᵐ ] t → 𝟘ᶜ ▸[ m ] t
𝟘ᶜ▸[𝟙ᵐ]→ {m = 𝟘ᵐ} = ▸-𝟘
𝟘ᶜ▸[𝟙ᵐ]→ {m = 𝟙ᵐ} = idᶠ

-- A form of monotonicity for _▸[_]_.

▸-≤ : p ≤ q → ⌜ ⌞ p ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p ⌟ ] t → ⌜ ⌞ q ⌟ ⌝ ·ᶜ γ ▸[ ⌞ q ⌟ ] t
▸-≤ {p = p} {q = q} {γ = γ} {t = t} p≤q = lemma _ _ refl refl
  where
  lemma :
    ∀ m₁ m₂ → ⌞ p ⌟ ≡ m₁ → ⌞ q ⌟ ≡ m₂ →
    ⌜ m₁ ⌝ ·ᶜ γ ▸[ m₁ ] t → ⌜ m₂ ⌝ ·ᶜ γ ▸[ m₂ ] t
  lemma 𝟘ᵐ 𝟘ᵐ _ _ ▸t = ▸-cong 𝟘ᵐ-cong ▸t
  lemma 𝟙ᵐ 𝟙ᵐ _ _ ▸t = ▸t
  lemma 𝟙ᵐ 𝟘ᵐ _ _ ▸t = sub (▸-𝟘 ▸t) (begin
    𝟘 ·ᶜ γ  ≈⟨ ·ᶜ-zeroˡ _ ⟩
    𝟘ᶜ      ∎)
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset
  lemma 𝟘ᵐ[ ok ] 𝟙ᵐ ⌞p⌟≡𝟘ᵐ ⌞q⌟≡𝟙ᵐ ▸t =
    ⊥-elim (⌞⌟≡𝟙ᵐ→≢𝟘 ok ⌞q⌟≡𝟙ᵐ (𝟘ᵐ.𝟘≮ ok (begin
      𝟘  ≈˘⟨ ⌞⌟≡𝟘ᵐ→≡𝟘 ⌞p⌟≡𝟘ᵐ ⟩
      p  ≤⟨ p≤q ⟩
      q  ∎)))
    where
    open Tools.Reasoning.PartialOrder ≤-poset

-- If t is well-resourced with respect to the usage context γ, then t
-- is well-resourced with respect to the mode ⌞ p ⌟ and some usage
-- context δ for which p ·ᶜ γ ≈ᶜ p ·ᶜ δ.

▸[𝟙ᵐ]→▸[⌞⌟] :
  γ ▸[ 𝟙ᵐ ] t →
  ∃ λ δ → δ ▸[ ⌞ p ⌟ ] t × p ·ᶜ γ ≈ᶜ p ·ᶜ δ
▸[𝟙ᵐ]→▸[⌞⌟] {γ = γ} {t = t} {p = p} ▸t = lemma _ refl
  where
  lemma : ∀ m → ⌞ p ⌟ ≡ m → ∃ λ δ → δ ▸[ m ] t × p ·ᶜ γ ≈ᶜ p ·ᶜ δ
  lemma 𝟙ᵐ       _      = _ , ▸t , ≈ᶜ-refl
  lemma 𝟘ᵐ[ ok ] ⌞p⌟≡𝟘ᵐ =
      _
    , ▸-𝟘 ▸t
    , (let open Tools.Reasoning.Equivalence Conₘ-setoid in begin
         p ·ᶜ γ   ≈⟨ ·ᶜ-congʳ (⌞⌟≡𝟘ᵐ→≡𝟘 ⌞p⌟≡𝟘ᵐ) ⟩
         𝟘 ·ᶜ γ   ≈⟨ ·ᶜ-zeroˡ _ ⟩
         𝟘ᶜ       ≈˘⟨ ·ᶜ-zeroʳ _ ⟩
         p ·ᶜ 𝟘ᶜ  ∎)

------------------------------------------------------------------------
-- Usage-restrictions-satisfied

-- Usage-restrictions-satisfied m t means that the usage restrictions
-- for Prodrec and Unitrec hold, for certain modes, for every subterm
-- in t.

data Usage-restrictions-satisfied {n} (m : Mode) : Term n → Set a where
  varᵤ :
    Usage-restrictions-satisfied m (var x)
  Emptyᵤ :
    Usage-restrictions-satisfied m Empty
  emptyrecᵤ :
    Usage-restrictions-satisfied 𝟘ᵐ? A →
    Usage-restrictions-satisfied (m ᵐ· p) t →
    Usage-restrictions-satisfied m (emptyrec p A t)
  Unitᵤ :
    Usage-restrictions-satisfied m (Unit str)
  starᵤ :
    Usage-restrictions-satisfied m (star str)
  unitrecᵤ :
    Unitrec-allowed m p q →
    Usage-restrictions-satisfied 𝟘ᵐ? A →
    Usage-restrictions-satisfied (m ᵐ· p) t →
    Usage-restrictions-satisfied m u →
    Usage-restrictions-satisfied m (unitrec p q A t u)
  ΠΣᵤ :
    Usage-restrictions-satisfied (m ᵐ· p) A →
    Usage-restrictions-satisfied m B →
    Usage-restrictions-satisfied m (ΠΣ⟨ bm ⟩ p , q ▷ A ▹ B)
  lamᵤ :
    Usage-restrictions-satisfied m t →
    Usage-restrictions-satisfied m (lam p t)
  ∘ᵤ :
    Usage-restrictions-satisfied m t →
    Usage-restrictions-satisfied (m ᵐ· p) u →
    Usage-restrictions-satisfied m (t ∘⟨ p ⟩ u)
  prodᵤ :
    Usage-restrictions-satisfied (m ᵐ· p) t →
    Usage-restrictions-satisfied m u →
    Usage-restrictions-satisfied m (prod str p t u)
  prodrecᵤ :
    Prodrec-allowed m r p q →
    Usage-restrictions-satisfied 𝟘ᵐ? A →
    Usage-restrictions-satisfied (m ᵐ· r) t →
    Usage-restrictions-satisfied m u →
    Usage-restrictions-satisfied m (prodrec r p q A t u)
  fstᵤ :
    Usage-restrictions-satisfied m t →
    Usage-restrictions-satisfied m (fst p t)
  sndᵤ :
    Usage-restrictions-satisfied m t →
    Usage-restrictions-satisfied m (snd p t)
  ℕᵤ :
    Usage-restrictions-satisfied m ℕ
  zeroᵤ :
    Usage-restrictions-satisfied m zero
  sucᵤ :
    Usage-restrictions-satisfied m t →
    Usage-restrictions-satisfied m (suc t)
  natrecᵤ :
    Usage-restrictions-satisfied 𝟘ᵐ? A →
    Usage-restrictions-satisfied m t →
    Usage-restrictions-satisfied m u →
    Usage-restrictions-satisfied m v →
    Usage-restrictions-satisfied m (natrec p q r A t u v)
  Uᵤ :
    Usage-restrictions-satisfied m U
  Idᵤ :
    ¬ Id-erased →
    Usage-restrictions-satisfied 𝟘ᵐ? A →
    Usage-restrictions-satisfied m t →
    Usage-restrictions-satisfied m u →
    Usage-restrictions-satisfied m (Id A t u)
  Id₀ᵤ :
    Id-erased →
    Usage-restrictions-satisfied 𝟘ᵐ? A →
    Usage-restrictions-satisfied 𝟘ᵐ? t →
    Usage-restrictions-satisfied 𝟘ᵐ? u →
    Usage-restrictions-satisfied m (Id A t u)
  rflᵤ :
    Usage-restrictions-satisfied m rfl
  Jᵤ :
    ¬ Erased-matches-for-J m →
    Usage-restrictions-satisfied 𝟘ᵐ? A →
    Usage-restrictions-satisfied m t →
    Usage-restrictions-satisfied m B →
    Usage-restrictions-satisfied m u →
    Usage-restrictions-satisfied m v →
    Usage-restrictions-satisfied m w →
    Usage-restrictions-satisfied m (J p q A t B u v w)
  J₀ᵤ :
    Erased-matches-for-J m →
    Usage-restrictions-satisfied 𝟘ᵐ? A →
    Usage-restrictions-satisfied 𝟘ᵐ? t →
    Usage-restrictions-satisfied 𝟘ᵐ? B →
    Usage-restrictions-satisfied m u →
    Usage-restrictions-satisfied 𝟘ᵐ? v →
    Usage-restrictions-satisfied 𝟘ᵐ? w →
    Usage-restrictions-satisfied m (J p q A t B u v w)
  Kᵤ :
    ¬ Erased-matches-for-K m →
    Usage-restrictions-satisfied 𝟘ᵐ? A →
    Usage-restrictions-satisfied m t →
    Usage-restrictions-satisfied m B →
    Usage-restrictions-satisfied m u →
    Usage-restrictions-satisfied m v →
    Usage-restrictions-satisfied m (K p A t B u v)
  K₀ᵤ :
    Erased-matches-for-K m →
    Usage-restrictions-satisfied 𝟘ᵐ? A →
    Usage-restrictions-satisfied 𝟘ᵐ? t →
    Usage-restrictions-satisfied 𝟘ᵐ? B →
    Usage-restrictions-satisfied m u →
    Usage-restrictions-satisfied 𝟘ᵐ? v →
    Usage-restrictions-satisfied m (K p A t B u v)
  []-congᵤ :
    Usage-restrictions-satisfied 𝟘ᵐ? A →
    Usage-restrictions-satisfied 𝟘ᵐ? t →
    Usage-restrictions-satisfied 𝟘ᵐ? u →
    Usage-restrictions-satisfied 𝟘ᵐ? v →
    Usage-restrictions-satisfied m ([]-cong str A t u v)

-- If t is well-resourced (with respect to any context and the
-- mode m), then Usage-restrictions-satisfied m t holds.

▸→Usage-restrictions-satisfied :
  γ ▸[ m ] t → Usage-restrictions-satisfied m t
▸→Usage-restrictions-satisfied = λ where
  var →
    varᵤ
  Emptyₘ →
    Emptyᵤ
  (emptyrecₘ ▸t ▸A) →
    emptyrecᵤ (▸→Usage-restrictions-satisfied ▸A)
      (▸→Usage-restrictions-satisfied ▸t)
  Unitₘ →
    Unitᵤ
  starʷₘ →
    starᵤ
  (starˢₘ _) →
    starᵤ
  (unitrecₘ ▸t ▸u ▸A ok) →
    unitrecᵤ ok
      (▸→Usage-restrictions-satisfied ▸A)
      (▸→Usage-restrictions-satisfied ▸t)
      (▸→Usage-restrictions-satisfied ▸u)
  (ΠΣₘ ▸A ▸B) →
    ΠΣᵤ (▸→Usage-restrictions-satisfied ▸A)
      (▸→Usage-restrictions-satisfied ▸B)
  (lamₘ ▸t) →
    lamᵤ (▸→Usage-restrictions-satisfied ▸t)
  (▸t ∘ₘ ▸u) →
    ∘ᵤ (▸→Usage-restrictions-satisfied ▸t)
      (▸→Usage-restrictions-satisfied ▸u)
  (prodʷₘ ▸t ▸u) →
    prodᵤ (▸→Usage-restrictions-satisfied ▸t)
      (▸→Usage-restrictions-satisfied ▸u)
  (prodˢₘ ▸t ▸u) →
    prodᵤ (▸→Usage-restrictions-satisfied ▸t)
      (▸→Usage-restrictions-satisfied ▸u)
  (prodrecₘ ▸t ▸u ▸A ok) →
    prodrecᵤ ok (▸→Usage-restrictions-satisfied ▸A)
      (▸→Usage-restrictions-satisfied ▸t)
      (▸→Usage-restrictions-satisfied ▸u)
  (fstₘ _ ▸t PE.refl _) →
    fstᵤ (▸→Usage-restrictions-satisfied ▸t)
  (sndₘ ▸t) →
    sndᵤ (▸→Usage-restrictions-satisfied ▸t)
  ℕₘ →
    ℕᵤ
  zeroₘ →
    zeroᵤ
  (sucₘ ▸t) →
    sucᵤ (▸→Usage-restrictions-satisfied ▸t)
  (natrecₘ ▸t ▸u ▸v ▸A) →
    natrecᵤ (▸→Usage-restrictions-satisfied ▸A)
      (▸→Usage-restrictions-satisfied ▸t)
      (▸→Usage-restrictions-satisfied ▸u)
      (▸→Usage-restrictions-satisfied ▸v)
  (natrec-no-nrₘ ▸t ▸u ▸v ▸A _ _ _ _) →
    natrecᵤ (▸→Usage-restrictions-satisfied ▸A)
      (▸→Usage-restrictions-satisfied ▸t)
      (▸→Usage-restrictions-satisfied ▸u)
      (▸→Usage-restrictions-satisfied ▸v)
  Uₘ →
    Uᵤ
  (Idₘ ok ▸A ▸t ▸u) →
    Idᵤ ok (▸→Usage-restrictions-satisfied ▸A)
      (▸→Usage-restrictions-satisfied ▸t)
      (▸→Usage-restrictions-satisfied ▸u)
  (Id₀ₘ ok ▸A ▸t ▸u) →
    Id₀ᵤ ok (▸→Usage-restrictions-satisfied ▸A)
      (▸→Usage-restrictions-satisfied ▸t)
      (▸→Usage-restrictions-satisfied ▸u)
  rflₘ →
    rflᵤ
  (Jₘ ok ▸A ▸t ▸B ▸u ▸v ▸w) →
    Jᵤ ok (▸→Usage-restrictions-satisfied ▸A)
      (▸→Usage-restrictions-satisfied ▸t)
      (▸→Usage-restrictions-satisfied ▸B)
      (▸→Usage-restrictions-satisfied ▸u)
      (▸→Usage-restrictions-satisfied ▸v)
      (▸→Usage-restrictions-satisfied ▸w)
  (J₀ₘ ok ▸A ▸t ▸B ▸u ▸v ▸w) →
    J₀ᵤ ok (▸→Usage-restrictions-satisfied ▸A)
      (▸→Usage-restrictions-satisfied ▸t)
      (▸→Usage-restrictions-satisfied ▸B)
      (▸→Usage-restrictions-satisfied ▸u)
      (▸→Usage-restrictions-satisfied ▸v)
      (▸→Usage-restrictions-satisfied ▸w)
  (Kₘ ok ▸A ▸t ▸B ▸u ▸v) →
    Kᵤ ok (▸→Usage-restrictions-satisfied ▸A)
      (▸→Usage-restrictions-satisfied ▸t)
      (▸→Usage-restrictions-satisfied ▸B)
      (▸→Usage-restrictions-satisfied ▸u)
      (▸→Usage-restrictions-satisfied ▸v)
  (K₀ₘ ok ▸A ▸t ▸B ▸u ▸v) →
    K₀ᵤ ok (▸→Usage-restrictions-satisfied ▸A)
      (▸→Usage-restrictions-satisfied ▸t)
      (▸→Usage-restrictions-satisfied ▸B)
      (▸→Usage-restrictions-satisfied ▸u)
      (▸→Usage-restrictions-satisfied ▸v)
  ([]-congₘ ▸A ▸t ▸u ▸v) →
    []-congᵤ (▸→Usage-restrictions-satisfied ▸A)
      (▸→Usage-restrictions-satisfied ▸t)
      (▸→Usage-restrictions-satisfied ▸u)
      (▸→Usage-restrictions-satisfied ▸v)
  (sub ▸t _) →
    ▸→Usage-restrictions-satisfied ▸t

-- If Usage-restrictions-satisfied 𝟘ᵐ[ ok ] t holds, then t is
-- well-resourced with respect to 𝟘ᶜ and 𝟘ᵐ[ ok ].

Usage-restrictions-satisfied→▸[𝟘ᵐ] :
  Usage-restrictions-satisfied 𝟘ᵐ[ ok ] t → 𝟘ᶜ ▸[ 𝟘ᵐ[ ok ] ] t
Usage-restrictions-satisfied→▸[𝟘ᵐ] {ok = 𝟘ᵐ-ok} = lemma
  where
  open import Graded.Modality.Dedicated-nr.Instance

  𝟘ᵐ?≡𝟘ᵐ′ : 𝟘ᵐ? ≡ 𝟘ᵐ[ 𝟘ᵐ-ok ]
  𝟘ᵐ?≡𝟘ᵐ′ = 𝟘ᵐ?≡𝟘ᵐ

  lemma :
    Usage-restrictions-satisfied 𝟘ᵐ[ 𝟘ᵐ-ok ] t →
    𝟘ᶜ ▸[ 𝟘ᵐ[ 𝟘ᵐ-ok ] ] t

  lemma-𝟘ᵐ? :
    Usage-restrictions-satisfied 𝟘ᵐ? t →
    𝟘ᶜ ▸[ 𝟘ᵐ? ] t
  lemma-𝟘ᵐ? =
    ▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ∘→
    lemma ∘→
    PE.subst (λ m → Usage-restrictions-satisfied m _) 𝟘ᵐ?≡𝟘ᵐ

  lemma = λ where
    (prodrecᵤ {r} {p} {q} ok A-ok t-ok u-ok) →
      sub (prodrecₘ (lemma t-ok)
             (sub (lemma u-ok) $
              let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
                𝟘ᶜ ∙ 𝟘 · r · p ∙ 𝟘 · r  ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ∙ ·-zeroˡ _ ⟩
                𝟘ᶜ                      ∎)
             (sub (lemma-𝟘ᵐ? A-ok) $
              let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
                𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · q  ≈⟨ ≈ᶜ-refl ∙ ·-congʳ (cong ⌜_⌝ 𝟘ᵐ?≡𝟘ᵐ′) ⟩
                𝟘ᶜ ∙ 𝟘 · q        ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
                𝟘ᶜ                ∎)
             ok) $
      let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
        𝟘ᶜ             ≈˘⟨ ·ᶜ-zeroʳ _ ⟩
        r ·ᶜ 𝟘ᶜ        ≈˘⟨ +ᶜ-identityʳ _ ⟩
        r ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ  ∎
    (ΠΣᵤ {q} A-ok B-ok) →
      sub (ΠΣₘ (lemma A-ok) $ sub (lemma B-ok) $
           let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
             𝟘ᶜ ∙ 𝟘 · q  ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
             𝟘ᶜ          ∎) $
      let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
        𝟘ᶜ        ≈˘⟨ +ᶜ-identityˡ _ ⟩
        𝟘ᶜ +ᶜ 𝟘ᶜ  ∎
    (lamᵤ {p} t-ok) →
      let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
      lamₘ $ sub (lemma t-ok) $ begin
        𝟘ᶜ ∙ 𝟘 · p  ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
        𝟘ᶜ          ∎
    (∘ᵤ {p} t-ok u-ok) →
      let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
      sub (lemma t-ok ∘ₘ lemma u-ok) $
      begin
        𝟘ᶜ             ≈˘⟨ ·ᶜ-zeroʳ _ ⟩
        p ·ᶜ 𝟘ᶜ        ≈˘⟨ +ᶜ-identityˡ _ ⟩
        𝟘ᶜ +ᶜ p ·ᶜ 𝟘ᶜ  ∎
    (prodᵤ {p} {str = 𝕤} t-ok u-ok) →
      let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
      sub (prodˢₘ (lemma t-ok) (lemma u-ok)) $
      begin
        𝟘ᶜ             ≈˘⟨ ∧ᶜ-idem _ ⟩
        𝟘ᶜ ∧ᶜ 𝟘ᶜ       ≈˘⟨ ∧ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
        p ·ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ  ∎
    (prodᵤ {p} {str = 𝕨} t-ok u-ok) →
      let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
      sub (prodʷₘ (lemma t-ok) (lemma u-ok)) $
      begin
        𝟘ᶜ             ≈˘⟨ +ᶜ-identityˡ _ ⟩
        𝟘ᶜ +ᶜ 𝟘ᶜ       ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
        p ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ  ∎
    (fstᵤ t-ok) →
      fstₘ 𝟘ᵐ[ 𝟘ᵐ-ok ] (lemma t-ok) refl (λ ())
    (sndᵤ t-ok) →
      sndₘ (lemma t-ok)
    (sucᵤ t-ok) →
      sucₘ (lemma t-ok)
    (natrecᵤ {p} {q} {r} A-ok t-ok u-ok v-ok) →
      let u-lemma =
            sub (lemma u-ok) $
            let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
              𝟘ᶜ ∙ 𝟘 · p ∙ 𝟘 · r  ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ∙ ·-zeroˡ _ ⟩
              𝟘ᶜ                  ∎
          A-lemma =
            sub (lemma-𝟘ᵐ? A-ok) $
            let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
              𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · q  ≈⟨ ≈ᶜ-refl ∙ ·-congʳ (cong ⌜_⌝ 𝟘ᵐ?≡𝟘ᵐ′) ⟩
              𝟘ᶜ ∙ 𝟘 · q        ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
              𝟘ᶜ                ∎
      in case dedicated-nr? of λ where
        does-have-nr →
          sub (natrecₘ (lemma t-ok) u-lemma (lemma v-ok) A-lemma) $
          let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
            𝟘ᶜ                ≈˘⟨ nrᶜ-𝟘ᶜ ⟩
            nrᶜ p r 𝟘ᶜ 𝟘ᶜ 𝟘ᶜ  ∎
        does-not-have-nr →
          natrec-no-nrₘ (lemma t-ok) u-lemma (lemma v-ok) A-lemma
            ≤ᶜ-refl (λ _ → ≤ᶜ-refl) ≤ᶜ-refl $
          let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
            𝟘ᶜ                        ≈˘⟨ +ᶜ-identityʳ _ ⟩
            𝟘ᶜ +ᶜ 𝟘ᶜ                  ≈˘⟨ +ᶜ-cong (·ᶜ-zeroʳ _) (·ᶜ-zeroʳ _) ⟩
            p ·ᶜ 𝟘ᶜ +ᶜ r ·ᶜ 𝟘ᶜ        ≈˘⟨ +ᶜ-identityˡ _ ⟩
            𝟘ᶜ +ᶜ p ·ᶜ 𝟘ᶜ +ᶜ r ·ᶜ 𝟘ᶜ  ∎
    (emptyrecᵤ {p} A-ok t-ok) →
      let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
      sub (emptyrecₘ (lemma t-ok) (lemma-𝟘ᵐ? A-ok)) $
      begin
        𝟘ᶜ       ≈˘⟨ ·ᶜ-zeroʳ _ ⟩
        p ·ᶜ 𝟘ᶜ  ∎
    (unitrecᵤ {p} {q} ok A-ok t-ok u-ok) →
      let A-lemma =
            sub (lemma-𝟘ᵐ? A-ok) $
            let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
              𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · q  ≈⟨ ≈ᶜ-refl ∙ ·-congʳ (cong ⌜_⌝ (𝟘ᵐ?≡𝟘ᵐ {ok = 𝟘ᵐ-ok})) ⟩
              𝟘ᶜ ∙ 𝟘 · q        ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
              𝟘ᶜ                ∎
      in  sub (unitrecₘ (lemma t-ok) (lemma u-ok) A-lemma ok) $
        let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
          𝟘ᶜ             ≈˘⟨ +ᶜ-identityˡ _ ⟩
          𝟘ᶜ +ᶜ 𝟘ᶜ       ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
          p ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ  ∎
    (Idᵤ not-erased A-ok t-ok u-ok) → sub
      (Idₘ not-erased
         (lemma-𝟘ᵐ? A-ok)
         (lemma t-ok)
         (lemma u-ok)) $
      let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
        𝟘ᶜ        ≈˘⟨ +ᶜ-identityˡ _ ⟩
        𝟘ᶜ +ᶜ 𝟘ᶜ  ∎
    (Id₀ᵤ erased A-ok t-ok u-ok) →
      Id₀ₘ erased
        (lemma-𝟘ᵐ? A-ok)
        (lemma-𝟘ᵐ? t-ok)
        (lemma-𝟘ᵐ? u-ok)
    (Jᵤ {p} {q} not-ok A-ok t-ok B-ok u-ok v-ok w-ok) → sub
      (Jₘ not-ok
         (lemma-𝟘ᵐ? A-ok)
         (lemma t-ok)
         (sub (lemma B-ok) $
          let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
            𝟘ᶜ ∙ 𝟘 · p ∙ 𝟘 · q  ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ∙ ·-zeroˡ _ ⟩
            𝟘ᶜ                  ∎)
         (lemma u-ok)
         (lemma v-ok)
         (lemma w-ok)) $
      let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
        𝟘ᶜ                                 ≈˘⟨ ω·ᶜ⋀ᶜ⁵𝟘ᶜ ⟩
        ω ·ᶜ (𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ)  ∎
    (J₀ᵤ {p} {q} ok A-ok t-ok B-ok u-ok v-ok w-ok) →
      J₀ₘ ok
        (lemma-𝟘ᵐ? A-ok)
        (lemma-𝟘ᵐ? t-ok)
        (sub (lemma-𝟘ᵐ? B-ok) $
         let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
           𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · p ∙ ⌜ 𝟘ᵐ? ⌝ · q  ≈⟨ ≈ᶜ-refl ∙ ·-congʳ (cong ⌜_⌝ 𝟘ᵐ?≡𝟘ᵐ′) ∙ ·-congʳ (cong ⌜_⌝ 𝟘ᵐ?≡𝟘ᵐ′) ⟩
           𝟘ᶜ ∙ 𝟘 · p ∙ 𝟘 · q              ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ∙ ·-zeroˡ _ ⟩
           𝟘ᶜ                              ∎)
        (lemma u-ok)
        (lemma-𝟘ᵐ? v-ok)
        (lemma-𝟘ᵐ? w-ok)
    (Kᵤ {p} not-ok A-ok t-ok B-ok u-ok v-ok) → sub
      (Kₘ not-ok
         (lemma-𝟘ᵐ? A-ok)
         (lemma t-ok)
         (sub (lemma B-ok) $
          let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
            𝟘ᶜ ∙ 𝟘 · p  ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
            𝟘ᶜ          ∎)
         (lemma u-ok)
         (lemma v-ok)) $
      let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
        𝟘ᶜ                           ≈˘⟨ ω·ᶜ⋀ᶜ⁴𝟘ᶜ ⟩
        ω ·ᶜ (𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ)  ∎
    (K₀ᵤ {p} ok A-ok t-ok B-ok u-ok v-ok) →
      K₀ₘ ok
        (lemma-𝟘ᵐ? A-ok)
        (lemma-𝟘ᵐ? t-ok)
        (sub (lemma-𝟘ᵐ? B-ok) $
         let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
           𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · p  ≈⟨ ≈ᶜ-refl ∙ ·-congʳ (cong ⌜_⌝ 𝟘ᵐ?≡𝟘ᵐ′) ⟩
           𝟘ᶜ ∙ 𝟘 · p        ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
           𝟘ᶜ                ∎)
        (lemma u-ok)
        (lemma-𝟘ᵐ? v-ok)
    ([]-congᵤ A-ok t-ok u-ok v-ok) →
      []-congₘ
        (lemma-𝟘ᵐ? A-ok)
        (lemma-𝟘ᵐ? t-ok)
        (lemma-𝟘ᵐ? u-ok)
        (lemma-𝟘ᵐ? v-ok)
    (varᵤ {x}) →
      let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
      sub var $ begin
        𝟘ᶜ          ≡˘⟨ 𝟘ᶜ,≔𝟘 ⟩
        𝟘ᶜ , x ≔ 𝟘  ∎
    Uᵤ →
      Uₘ
    ℕᵤ →
      ℕₘ
    Emptyᵤ →
      Emptyₘ
    Unitᵤ →
      Unitₘ
    zeroᵤ →
      zeroₘ
    starᵤ →
      starₘ
    rflᵤ →
      rflₘ

-- An alternative characterisation of 𝟘ᶜ ▸[ 𝟘ᵐ[ ok ] ] t.

𝟘ᶜ▸[𝟘ᵐ]⇔ : 𝟘ᶜ ▸[ 𝟘ᵐ[ ok ] ] t ⇔ Usage-restrictions-satisfied 𝟘ᵐ[ ok ] t
𝟘ᶜ▸[𝟘ᵐ]⇔ =
    ▸→Usage-restrictions-satisfied
  , Usage-restrictions-satisfied→▸[𝟘ᵐ]

-- If γ ▸[ 𝟘ᵐ[ ok ] ] t, then γ ≤ᶜ 𝟘ᶜ.

▸-𝟘ᵐ : γ ▸[ 𝟘ᵐ[ ok ] ] t → γ ≤ᶜ 𝟘ᶜ
▸-𝟘ᵐ Uₘ =
  ≤ᶜ-refl
▸-𝟘ᵐ ℕₘ =
  ≤ᶜ-refl
▸-𝟘ᵐ Emptyₘ =
  ≤ᶜ-refl
▸-𝟘ᵐ Unitₘ =
  ≤ᶜ-refl
▸-𝟘ᵐ (ΠΣₘ {γ = γ} {δ = δ} γ▸ δ▸) = begin
  γ +ᶜ δ    ≤⟨ +ᶜ-monotone (▸-𝟘ᵐ γ▸) (tailₘ-monotone (▸-𝟘ᵐ δ▸)) ⟩
  𝟘ᶜ +ᶜ 𝟘ᶜ  ≈⟨ +ᶜ-identityˡ _ ⟩
  𝟘ᶜ        ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
▸-𝟘ᵐ (var {x = x}) = begin
  𝟘ᶜ , x ≔ 𝟘  ≡⟨ 𝟘ᶜ,≔𝟘 ⟩
  𝟘ᶜ          ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
▸-𝟘ᵐ (lamₘ γ▸) =
  tailₘ-monotone (▸-𝟘ᵐ γ▸)
▸-𝟘ᵐ (_∘ₘ_ {γ = γ} {δ = δ} {p = p} γ▸ δ▸) = begin
  γ +ᶜ p ·ᶜ δ    ≤⟨ +ᶜ-monotone (▸-𝟘ᵐ γ▸) (·ᶜ-monotoneʳ (▸-𝟘ᵐ δ▸)) ⟩
  𝟘ᶜ +ᶜ p ·ᶜ 𝟘ᶜ  ≈⟨ +ᶜ-identityˡ _ ⟩
  p ·ᶜ 𝟘ᶜ        ≈⟨ ·ᶜ-zeroʳ _ ⟩
  𝟘ᶜ             ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
▸-𝟘ᵐ (prodʷₘ {γ = γ} {p = p} {δ = δ} γ▸ δ▸) = begin
  p ·ᶜ γ +ᶜ δ    ≤⟨ +ᶜ-monotone (·ᶜ-monotoneʳ (▸-𝟘ᵐ γ▸)) (▸-𝟘ᵐ δ▸) ⟩
  p ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ  ≈⟨ +ᶜ-identityʳ _ ⟩
  p ·ᶜ 𝟘ᶜ        ≈⟨ ·ᶜ-zeroʳ _ ⟩
  𝟘ᶜ             ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
▸-𝟘ᵐ (prodˢₘ {γ = γ} {p = p} {δ = δ} γ▸ δ▸) = begin
  p ·ᶜ γ ∧ᶜ δ    ≤⟨ ∧ᶜ-monotone (·ᶜ-monotoneʳ (▸-𝟘ᵐ γ▸)) (▸-𝟘ᵐ δ▸) ⟩
  p ·ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ  ≈⟨ ∧ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
  𝟘ᶜ ∧ᶜ 𝟘ᶜ       ≈⟨ ∧ᶜ-idem _ ⟩
  𝟘ᶜ             ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
▸-𝟘ᵐ (fstₘ _ γ▸ eq _) = lemma γ▸ eq
  where
  lemma : γ ▸[ m ] t → m ≡ 𝟘ᵐ[ ok ] → γ ≤ᶜ 𝟘ᶜ
  lemma γ▸ refl = ▸-𝟘ᵐ γ▸
▸-𝟘ᵐ (sndₘ γ▸) =
  ▸-𝟘ᵐ γ▸
▸-𝟘ᵐ (prodrecₘ {γ = γ} {r = r} {δ = δ} γ▸ δ▸ _ _) = begin
  r ·ᶜ γ +ᶜ δ    ≤⟨ +ᶜ-monotone (·ᶜ-monotoneʳ (▸-𝟘ᵐ γ▸)) (tailₘ-monotone (tailₘ-monotone (▸-𝟘ᵐ δ▸))) ⟩
  r ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ  ≈⟨ +ᶜ-identityʳ _ ⟩
  r ·ᶜ 𝟘ᶜ        ≈⟨ ·ᶜ-zeroʳ _ ⟩
  𝟘ᶜ             ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
▸-𝟘ᵐ zeroₘ =
  ≤ᶜ-refl
▸-𝟘ᵐ (sucₘ γ▸) =
  ▸-𝟘ᵐ γ▸
▸-𝟘ᵐ
  (natrecₘ {γ = γ} {δ = δ} {p = p} {r = r} {η = η} γ▸ δ▸ η▸ _) = begin
  nrᶜ p r γ δ η     ≤⟨ nrᶜ-monotone (▸-𝟘ᵐ γ▸) (tailₘ-monotone (tailₘ-monotone (▸-𝟘ᵐ δ▸))) (▸-𝟘ᵐ η▸) ⟩
  nrᶜ p r 𝟘ᶜ 𝟘ᶜ 𝟘ᶜ  ≈⟨ nrᶜ-𝟘ᶜ ⟩
  𝟘ᶜ                ∎
  where
  open import Graded.Modality.Dedicated-nr.Instance
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
▸-𝟘ᵐ
  (natrec-no-nrₘ {γ = γ} {χ = χ} γ▸ _ _ _ χ≤γ _ _ _) = begin
  χ   ≤⟨ χ≤γ ⟩
  γ   ≤⟨ ▸-𝟘ᵐ γ▸ ⟩
  𝟘ᶜ  ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
▸-𝟘ᵐ (emptyrecₘ {γ = γ} {p = p} γ▸ _) = begin
  p ·ᶜ γ   ≤⟨ ·ᶜ-monotoneʳ (▸-𝟘ᵐ γ▸) ⟩
  p ·ᶜ 𝟘ᶜ  ≈⟨ ·ᶜ-zeroʳ _ ⟩
  𝟘ᶜ       ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
▸-𝟘ᵐ starʷₘ = ≤ᶜ-refl
▸-𝟘ᵐ (starˢₘ prop) = ≤ᶜ-reflexive (·ᶜ-zeroˡ _)
▸-𝟘ᵐ (unitrecₘ {γ = γ} {p = p} {δ = δ} γ▸ δ▸ η▸ ok) = begin
  p ·ᶜ γ +ᶜ δ     ≤⟨ +ᶜ-monotone (·ᶜ-monotoneʳ (▸-𝟘ᵐ γ▸)) (▸-𝟘ᵐ δ▸) ⟩
  p ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ  ≈⟨ +ᶜ-identityʳ _ ⟩
  p ·ᶜ 𝟘ᶜ        ≈⟨ ·ᶜ-zeroʳ _ ⟩
  𝟘ᶜ             ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
▸-𝟘ᵐ (Idₘ {δ = δ} {η = η} _ _ δ▸ η▸) = begin
  δ +ᶜ η    ≤⟨ +ᶜ-monotone (▸-𝟘ᵐ δ▸) (▸-𝟘ᵐ η▸) ⟩
  𝟘ᶜ +ᶜ 𝟘ᶜ  ≈⟨ +ᶜ-identityʳ _ ⟩
  𝟘ᶜ        ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
▸-𝟘ᵐ (Id₀ₘ _ _ _ _) =
  ≤ᶜ-refl
▸-𝟘ᵐ rflₘ =
  ≤ᶜ-refl
▸-𝟘ᵐ (Jₘ {γ₂} {γ₃} {γ₄} {γ₅} {γ₆} _ _ γ₂▸ γ₃▸ γ₄▸ γ₅▸ γ₆▸) = begin
  ω ·ᶜ (γ₂ ∧ᶜ γ₃ ∧ᶜ γ₄ ∧ᶜ γ₅ ∧ᶜ γ₆)  ≤⟨ ·ᶜ-monotoneʳ $
                                        ∧ᶜ-monotone (▸-𝟘ᵐ γ₂▸) $
                                        ∧ᶜ-monotone (tailₘ-monotone (tailₘ-monotone (▸-𝟘ᵐ γ₃▸))) $
                                        ∧ᶜ-monotone (▸-𝟘ᵐ γ₄▸) $
                                        ∧ᶜ-monotone (▸-𝟘ᵐ γ₅▸) (▸-𝟘ᵐ γ₆▸) ⟩
  ω ·ᶜ (𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ)  ≈⟨ ω·ᶜ⋀ᶜ⁵𝟘ᶜ ⟩
  𝟘ᶜ                                 ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
▸-𝟘ᵐ (J₀ₘ _ _ _ _ γ₄▸ _ _) =
  ▸-𝟘ᵐ γ₄▸
▸-𝟘ᵐ (Kₘ {γ₂} {γ₃} {γ₄} {γ₅} _ _ γ₂▸ γ₃▸ γ₄▸ γ₅▸) = begin
  ω ·ᶜ (γ₂ ∧ᶜ γ₃ ∧ᶜ γ₄ ∧ᶜ γ₅)  ≤⟨ ·ᶜ-monotoneʳ $
                                  ∧ᶜ-monotone (▸-𝟘ᵐ γ₂▸) $
                                  ∧ᶜ-monotone (tailₘ-monotone (▸-𝟘ᵐ γ₃▸)) $
                                  ∧ᶜ-monotone (▸-𝟘ᵐ γ₄▸) (▸-𝟘ᵐ γ₅▸) ⟩
  ω ·ᶜ (𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ)  ≈⟨ ω·ᶜ⋀ᶜ⁴𝟘ᶜ ⟩
  𝟘ᶜ                           ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
▸-𝟘ᵐ (K₀ₘ _ _ _ _ γ₄▸ _) =
  ▸-𝟘ᵐ γ₄▸
▸-𝟘ᵐ ([]-congₘ _ _ _ _) =
  ≤ᶜ-refl
▸-𝟘ᵐ (sub {γ = γ} {δ = δ} γ▸ δ≤γ) = begin
  δ   ≤⟨ δ≤γ ⟩
  γ   ≤⟨ ▸-𝟘ᵐ γ▸ ⟩
  𝟘ᶜ  ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- An alternative characterisation of γ ▸[ 𝟘ᵐ[ ok ] ] t.

▸[𝟘ᵐ]⇔ :
  γ ▸[ 𝟘ᵐ[ ok ] ] t ⇔
  (γ ≤ᶜ 𝟘ᶜ × Usage-restrictions-satisfied 𝟘ᵐ[ ok ] t)
▸[𝟘ᵐ]⇔ =
    (λ ▸t → ▸-𝟘ᵐ ▸t , ▸→Usage-restrictions-satisfied ▸t)
  , (λ (γ≤𝟘 , ok) → sub (Usage-restrictions-satisfied→▸[𝟘ᵐ] ok) γ≤𝟘)

opaque

  -- If the modality is trivial and Usage-restrictions-satisfied m t
  -- holds, then γ ▸[ m ] t holds.

  Trivial→Usage-restrictions-satisfied→▸ :
    Trivial → Usage-restrictions-satisfied m t → γ ▸[ m ] t
  Trivial→Usage-restrictions-satisfied→▸ 𝟙≡𝟘 = lemma
    where mutual
    lemma₀ : Usage-restrictions-satisfied m t → 𝟘ᶜ ▸[ m ] t
    lemma₀ = lemma

    lemma : Usage-restrictions-satisfied m t → γ ▸[ m ] t
    lemma = λ where
      (prodrecᵤ ok A-ok t-ok u-ok) →
        sub
          (prodrecₘ {δ = 𝟘ᶜ} {η = 𝟘ᶜ} (lemma₀ t-ok) (lemma u-ok)
             (lemma A-ok) ok)
          (≈ᶜ-trivial 𝟙≡𝟘)
      (ΠΣᵤ A-ok B-ok) →
        sub (ΠΣₘ {δ = 𝟘ᶜ} (lemma₀ A-ok) (lemma B-ok))
          (≈ᶜ-trivial 𝟙≡𝟘)
      (lamᵤ t-ok) →
        lamₘ (lemma t-ok)
      (∘ᵤ t-ok u-ok) →
        sub (lemma₀ t-ok ∘ₘ lemma₀ u-ok) (≈ᶜ-trivial 𝟙≡𝟘)
      (prodᵤ {str = 𝕤} t-ok u-ok) →
        sub (prodˢₘ (lemma₀ t-ok) (lemma₀ u-ok)) (≈ᶜ-trivial 𝟙≡𝟘)
      (prodᵤ {str = 𝕨} t-ok u-ok) →
        sub (prodʷₘ (lemma₀ t-ok) (lemma₀ u-ok)) (≈ᶜ-trivial 𝟙≡𝟘)
      (fstᵤ t-ok) →
        fstₘ 𝟙ᵐ
          (▸-cong (Mode-propositional-if-trivial 𝟙≡𝟘) (lemma t-ok))
          (Mode-propositional-if-trivial 𝟙≡𝟘)
          (λ _ → ≡-trivial 𝟙≡𝟘)
      (sndᵤ t-ok) →
        sndₘ (lemma t-ok)
      (sucᵤ t-ok) →
        sucₘ (lemma t-ok)
      (natrecᵤ A-ok t-ok u-ok v-ok) →
        case dedicated-nr? of λ where
          does-have-nr →
            sub
              (natrecₘ {δ = 𝟘ᶜ} {θ = 𝟘ᶜ} (lemma₀ t-ok) (lemma u-ok)
                 (lemma₀ v-ok) (lemma A-ok))
              (≈ᶜ-trivial 𝟙≡𝟘)
          does-not-have-nr →
            natrec-no-nrₘ {δ = 𝟘ᶜ} {θ = 𝟘ᶜ} (lemma₀ t-ok) (lemma u-ok)
              (lemma₀ v-ok) (lemma A-ok) (≈ᶜ-trivial 𝟙≡𝟘)
              (λ _ → ≈ᶜ-trivial 𝟙≡𝟘) (≈ᶜ-trivial 𝟙≡𝟘) (≈ᶜ-trivial 𝟙≡𝟘)
      (emptyrecᵤ A-ok t-ok) →
        sub (emptyrecₘ (lemma₀ t-ok) (lemma₀ A-ok)) (≈ᶜ-trivial 𝟙≡𝟘)
      (unitrecᵤ ok A-ok t-ok u-ok) →
        sub
          (unitrecₘ {η = 𝟘ᶜ} (lemma₀ t-ok) (lemma₀ u-ok) (lemma A-ok)
             ok)
          (≈ᶜ-trivial 𝟙≡𝟘)
      (Idᵤ not-erased A-ok t-ok u-ok) →
        sub
          (Idₘ not-erased (lemma₀ A-ok) (lemma₀ t-ok) (lemma₀ u-ok))
          (≈ᶜ-trivial 𝟙≡𝟘)
      (Id₀ᵤ erased A-ok t-ok u-ok) →
        sub
          (Id₀ₘ erased (lemma₀ A-ok) (lemma₀ t-ok) (lemma₀ u-ok))
          (≈ᶜ-trivial 𝟙≡𝟘)
      (Jᵤ not-ok A-ok t-ok B-ok u-ok v-ok w-ok) →
        sub
          (Jₘ {γ₃ = 𝟘ᶜ} not-ok (lemma₀ A-ok) (lemma₀ t-ok) (lemma B-ok)
             (lemma₀ u-ok) (lemma₀ v-ok) (lemma₀ w-ok))
          (≈ᶜ-trivial 𝟙≡𝟘)
      (J₀ᵤ ok A-ok t-ok B-ok u-ok v-ok w-ok) →
        sub
          (J₀ₘ {γ₃ = 𝟘ᶜ} ok (lemma₀ A-ok) (lemma₀ t-ok) (lemma B-ok)
             (lemma₀ u-ok) (lemma₀ v-ok) (lemma₀ w-ok))
          (≈ᶜ-trivial 𝟙≡𝟘)
      (Kᵤ not-ok A-ok t-ok B-ok u-ok v-ok) →
        sub
          (Kₘ {γ₃ = 𝟘ᶜ} not-ok (lemma₀ A-ok) (lemma₀ t-ok) (lemma B-ok)
             (lemma₀ u-ok) (lemma₀ v-ok))
          (≈ᶜ-trivial 𝟙≡𝟘)
      (K₀ᵤ ok A-ok t-ok B-ok u-ok v-ok) →
        sub
          (K₀ₘ {γ₃ = 𝟘ᶜ} ok (lemma₀ A-ok) (lemma₀ t-ok) (lemma B-ok)
             (lemma₀ u-ok) (lemma₀ v-ok))
          (≈ᶜ-trivial 𝟙≡𝟘)
      ([]-congᵤ A-ok t-ok u-ok v-ok) →
        sub
          ([]-congₘ (lemma₀ A-ok) (lemma₀ t-ok) (lemma₀ u-ok)
             (lemma₀ v-ok))
          (≈ᶜ-trivial 𝟙≡𝟘)
      varᵤ →
        sub var (≈ᶜ-trivial 𝟙≡𝟘)
      Uᵤ →
        sub Uₘ (≈ᶜ-trivial 𝟙≡𝟘)
      ℕᵤ →
        sub ℕₘ (≈ᶜ-trivial 𝟙≡𝟘)
      Emptyᵤ →
        sub Emptyₘ (≈ᶜ-trivial 𝟙≡𝟘)
      Unitᵤ →
        sub Unitₘ (≈ᶜ-trivial 𝟙≡𝟘)
      zeroᵤ →
        sub zeroₘ (≈ᶜ-trivial 𝟙≡𝟘)
      starᵤ →
        sub starₘ (≈ᶜ-trivial 𝟙≡𝟘)
      rflᵤ →
        sub rflₘ (≈ᶜ-trivial 𝟙≡𝟘)

opaque

  -- An alternative characterisation of γ ▸[ m ] t for trivial
  -- modalities.

  Trivial→▸⇔ : Trivial → γ ▸[ m ] t ⇔ Usage-restrictions-satisfied m t
  Trivial→▸⇔ 𝟙≡𝟘 =
      ▸→Usage-restrictions-satisfied
    , Trivial→Usage-restrictions-satisfied→▸ 𝟙≡𝟘

------------------------------------------------------------------------
-- Inversion lemmas

-- A kind of inversion lemma for _▸[_]_ related to multiplication.

▸-⌞·⌟ :
  ⌜ ⌞ p · q ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p · q ⌟ ] t →
  (⌜ ⌞ p ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p ⌟ ] t) ⊎ (⌜ ⌞ q ⌟ ⌝ ·ᶜ γ ▸[ ⌞ q ⌟ ] t)
▸-⌞·⌟ {p = p} {q = q} {γ = γ} ▸t =
  lemma _ _ refl refl
    (subst (λ m → ⌜ m ⌝ ·ᶜ _ ▸[ m ] _) (PE.sym ⌞⌟·ᵐ) ▸t)
  where
  lemma :
    ∀ m₁ m₂ → ⌞ p ⌟ ≡ m₁ → ⌞ q ⌟ ≡ m₂ →
    ⌜ m₁ ·ᵐ m₂ ⌝ ·ᶜ γ ▸[ m₁ ·ᵐ m₂ ] t →
    (⌜ m₁ ⌝ ·ᶜ γ ▸[ m₁ ] t) ⊎ (⌜ m₂ ⌝ ·ᶜ γ ▸[ m₂ ] t)
  lemma 𝟘ᵐ _  _ _ ▸t = inj₁ ▸t
  lemma 𝟙ᵐ 𝟘ᵐ _ _ ▸t = inj₂ ▸t
  lemma 𝟙ᵐ 𝟙ᵐ _ _ ▸t = inj₁ ▸t

-- If m₂ is 𝟘ᵐ[ ok ] whenever m₁ is 𝟘ᵐ[ ok ], then one can convert
-- from ⌜ m₁ ⌝ ·ᶜ γ ▸[ m₁ ] t to ⌜ m₂ ⌝ ·ᶜ γ ▸[ m₂ ] t.

▸-conv :
  (∀ ok → m₁ ≡ 𝟘ᵐ[ ok ] → m₂ ≡ 𝟘ᵐ[ ok ]) →
  ⌜ m₁ ⌝ ·ᶜ γ ▸[ m₁ ] t →
  ⌜ m₂ ⌝ ·ᶜ γ ▸[ m₂ ] t
▸-conv {m₁ = 𝟘ᵐ} {m₂ = 𝟘ᵐ} _ ▸t =
  ▸-cong 𝟘ᵐ-cong ▸t
▸-conv {m₁ = 𝟙ᵐ} {m₂ = 𝟙ᵐ} _ ▸t =
  ▸t
▸-conv {m₁ = 𝟘ᵐ} {m₂ = 𝟙ᵐ} 𝟘ᵐ≡𝟘ᵐ→𝟙ᵐ≡𝟘ᵐ ▸t =
  case 𝟘ᵐ≡𝟘ᵐ→𝟙ᵐ≡𝟘ᵐ _ PE.refl of λ ()
▸-conv {m₁ = 𝟙ᵐ} {m₂ = 𝟘ᵐ} {γ = γ} hyp ▸t = sub
  (▸-· {m′ = 𝟘ᵐ} ▸t)
  (begin
    𝟘 ·ᶜ γ       ≈˘⟨ ·ᶜ-congˡ (·ᶜ-identityˡ _) ⟩
    𝟘 ·ᶜ 𝟙 ·ᶜ γ  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- A kind of inversion lemma for _▸[_]_ related to addition.

▸-⌞+⌟ˡ :
  ⌜ ⌞ p + q ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p + q ⌟ ] t →
  ⌜ ⌞ p ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p ⌟ ] t
▸-⌞+⌟ˡ = ▸-conv λ ok ⌞p+q⌟≡𝟘ᵐ →
  ≡𝟘→⌞⌟≡𝟘ᵐ (𝟘ᵐ.+-positiveˡ ok (⌞⌟≡𝟘ᵐ→≡𝟘 ⌞p+q⌟≡𝟘ᵐ))

-- A kind of inversion lemma for _▸[_]_ related to addition.

▸-⌞+⌟ʳ :
  ⌜ ⌞ p + q ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p + q ⌟ ] t →
  ⌜ ⌞ q ⌟ ⌝ ·ᶜ γ ▸[ ⌞ q ⌟ ] t
▸-⌞+⌟ʳ ▸t =
  ▸-⌞+⌟ˡ (subst (λ m → ⌜ m ⌝ ·ᶜ _ ▸[ m ] _) (⌞⌟-cong (+-comm _ _)) ▸t)

-- A kind of inversion lemma for _▸[_]_ related to the meet operation.

▸-⌞∧⌟ˡ :
  ⌜ ⌞ p ∧ q ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p ∧ q ⌟ ] t →
  ⌜ ⌞ p ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p ⌟ ] t
▸-⌞∧⌟ˡ = ▸-conv λ ok ⌞p∧q⌟≡𝟘ᵐ →
  ≡𝟘→⌞⌟≡𝟘ᵐ (𝟘ᵐ.∧-positiveˡ ok (⌞⌟≡𝟘ᵐ→≡𝟘 ⌞p∧q⌟≡𝟘ᵐ))

-- A kind of inversion lemma for _▸[_]_ related to the meet operation.

▸-⌞∧⌟ʳ :
  ⌜ ⌞ p ∧ q ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p ∧ q ⌟ ] t →
  ⌜ ⌞ q ⌟ ⌝ ·ᶜ γ ▸[ ⌞ q ⌟ ] t
▸-⌞∧⌟ʳ ▸t =
  ▸-⌞∧⌟ˡ (subst (λ m → ⌜ m ⌝ ·ᶜ _ ▸[ m ] _) (⌞⌟-cong (∧-comm _ _)) ▸t)

-- A kind of inversion lemma for _▸[_]_ related to the star operation.

▸-⌞⊛⌟ˡ :
  ⦃ has-star : Has-star semiring-with-meet ⦄ →
  ⌜ ⌞ p ⊛ q ▷ r ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p ⊛ q ▷ r ⌟ ] t →
  ⌜ ⌞ p ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p ⌟ ] t
▸-⌞⊛⌟ˡ = ▸-conv λ ok ⌞p⊛q▷r⌟≡𝟘ᵐ →
  ≡𝟘→⌞⌟≡𝟘ᵐ (𝟘ᵐ.⊛≡𝟘ˡ ok (⌞⌟≡𝟘ᵐ→≡𝟘 ⌞p⊛q▷r⌟≡𝟘ᵐ))

-- A kind of inversion lemma for _▸[_]_ related to the star operation.

▸-⌞⊛⌟ʳ :
  ⦃ has-star : Has-star semiring-with-meet ⦄ →
  ⌜ ⌞ p ⊛ q ▷ r ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p ⊛ q ▷ r ⌟ ] t →
  ⌜ ⌞ q ⌟ ⌝ ·ᶜ γ ▸[ ⌞ q ⌟ ] t
▸-⌞⊛⌟ʳ = ▸-conv λ ok ⌞p⊛q▷r⌟≡𝟘ᵐ →
  ≡𝟘→⌞⌟≡𝟘ᵐ (𝟘ᵐ.⊛≡𝟘ʳ ok (⌞⌟≡𝟘ᵐ→≡𝟘 ⌞p⊛q▷r⌟≡𝟘ᵐ))

-- A kind of inversion lemma for _▸[_]_ related to the nr function.

▸-⌞nr⌟₁ :
  ∀ {n} ⦃ has-nr : Has-nr semiring-with-meet ⦄ →
  ⌜ ⌞ nr p r z s n ⌟ ⌝ ·ᶜ γ ▸[ ⌞ nr p r z s n ⌟ ] t →
  ⌜ ⌞ z ⌟ ⌝ ·ᶜ γ ▸[ ⌞ z ⌟ ] t
▸-⌞nr⌟₁ = ▸-conv λ ok ⌞nr-przsn⌟≡𝟘ᵐ →
  ≡𝟘→⌞⌟≡𝟘ᵐ $
  nr-positive ⦃ 𝟘-well-behaved = 𝟘-well-behaved ok ⦄
    (⌞⌟≡𝟘ᵐ→≡𝟘 ⌞nr-przsn⌟≡𝟘ᵐ) .proj₁

-- A kind of inversion lemma for _▸[_]_ related to the nr function.

▸-⌞nr⌟₂ :
  ∀ {n} ⦃ has-nr : Has-nr semiring-with-meet ⦄ →
  ⌜ ⌞ nr p r z s n ⌟ ⌝ ·ᶜ γ ▸[ ⌞ nr p r z s n ⌟ ] t →
  ⌜ ⌞ s ⌟ ⌝ ·ᶜ γ ▸[ ⌞ s ⌟ ] t
▸-⌞nr⌟₂ = ▸-conv λ ok ⌞nr-przsn⌟≡𝟘ᵐ →
  ≡𝟘→⌞⌟≡𝟘ᵐ $
  nr-positive ⦃ 𝟘-well-behaved = 𝟘-well-behaved ok ⦄
    (⌞⌟≡𝟘ᵐ→≡𝟘 ⌞nr-przsn⌟≡𝟘ᵐ) .proj₂ .proj₁

-- A kind of inversion lemma for _▸[_]_ related to the nr function.

▸-⌞nr⌟₃ :
  ∀ {n} ⦃ has-nr : Has-nr semiring-with-meet ⦄ →
  ⌜ ⌞ nr p r z s n ⌟ ⌝ ·ᶜ γ ▸[ ⌞ nr p r z s n ⌟ ] t →
  ⌜ ⌞ n ⌟ ⌝ ·ᶜ γ ▸[ ⌞ n ⌟ ] t
▸-⌞nr⌟₃ = ▸-conv λ ok ⌞nr-przsn⌟≡𝟘ᵐ →
  ≡𝟘→⌞⌟≡𝟘ᵐ $
  nr-positive ⦃ 𝟘-well-behaved = 𝟘-well-behaved ok ⦄
    (⌞⌟≡𝟘ᵐ→≡𝟘 ⌞nr-przsn⌟≡𝟘ᵐ) .proj₂ .proj₂

------------------------------------------------------------------------
-- The lemma Conₘ-interchange

-- The contents of two valid modality contexts can be freely
-- interchanged.

Conₘ-interchange :
  γ ▸[ m ] t → δ ▸[ m ] t → (x : Fin n) → (γ , x ≔ δ ⟨ x ⟩) ▸[ m ] t
Conₘ-interchange (sub γ▸t γ≤γ′) δ▸t x  = sub
  (Conₘ-interchange γ▸t δ▸t x)
  (update-monotoneˡ x γ≤γ′)
Conₘ-interchange γ▸t (sub γ′▸t δ≤γ′) x = sub
  (Conₘ-interchange γ▸t γ′▸t x)
  (update-monotoneʳ x (lookup-monotone x δ≤γ′))
Conₘ-interchange Uₘ Uₘ x =
  subst (_▸[ _ ] _) (PE.sym (update-self 𝟘ᶜ x)) Uₘ
Conₘ-interchange ℕₘ ℕₘ x =
  subst (_▸[ _ ] _) (PE.sym (update-self 𝟘ᶜ x)) ℕₘ
Conₘ-interchange Emptyₘ Emptyₘ x =
  subst (_▸[ _ ] _) (PE.sym (update-self 𝟘ᶜ x)) Emptyₘ
Conₘ-interchange Unitₘ Unitₘ x =
  subst (_▸[ _ ] _) (PE.sym (update-self 𝟘ᶜ x)) Unitₘ

Conₘ-interchange
  (ΠΣₘ {γ = γ} {δ = δ} γ▸t δ▸u)
  (ΠΣₘ {γ = γ′} {δ = δ′} γ′▸t δ′▸u) x =
  subst (_▸[ _ ] _)
    (begin
       (γ , x ≔ γ′ ⟨ x ⟩) +ᶜ (δ , x ≔ δ′ ⟨ x ⟩)  ≡˘⟨ update-distrib-+ᶜ γ _ _ _ x ⟩
       γ +ᶜ δ , x ≔ γ′ ⟨ x ⟩ + δ′ ⟨ x ⟩          ≡˘⟨ cong (_ , x ≔_) (lookup-distrib-+ᶜ γ′ _ _) ⟩
       γ +ᶜ δ , x ≔ (γ′ +ᶜ δ′) ⟨ x ⟩             ∎)
    (ΠΣₘ (Conₘ-interchange γ▸t γ′▸t x)
       (Conₘ-interchange δ▸u δ′▸u (x +1)))
  where
  open Tools.Reasoning.PropositionalEquality

Conₘ-interchange (var {x = y}) var x = subst (_▸[ _ ] _)
  (PE.sym (update-self (𝟘ᶜ , y ≔ _) x)) var

Conₘ-interchange (lamₘ γ▸t) (lamₘ δ▸t) x = lamₘ (Conₘ-interchange γ▸t δ▸t (x +1))

Conₘ-interchange
  (_∘ₘ_ {γ = γ} {δ = δ} {p = p} γ▸t δ▸u)
  (_∘ₘ_ {γ = γ′} {δ = δ′} γ′▸t δ′▸u)
  x =
  subst (_▸[ _ ] _) eq
    (Conₘ-interchange γ▸t γ′▸t x ∘ₘ
     Conₘ-interchange δ▸u δ′▸u x)
  where
  open Tools.Reasoning.PropositionalEquality
  eq = begin
    (γ , x ≔ (γ′ ⟨ x ⟩)) +ᶜ p ·ᶜ (δ , x ≔ (δ′ ⟨ x ⟩))
       ≡˘⟨ cong (_ +ᶜ_) (update-distrib-·ᶜ δ p _ x) ⟩
    (γ , x ≔ (γ′ ⟨ x ⟩)) +ᶜ (p ·ᶜ δ , x ≔ (p · δ′ ⟨ x ⟩))
       ≡˘⟨ cong (_ +ᶜ_) (cong (_ , x ≔_) (lookup-distrib-·ᶜ δ′ p x)) ⟩
    (γ , x ≔ (γ′ ⟨ x ⟩)) +ᶜ (p ·ᶜ δ , x ≔ ((p ·ᶜ δ′) ⟨ x ⟩))
       ≡˘⟨ update-distrib-+ᶜ γ _ _ _ x ⟩
    (γ +ᶜ p ·ᶜ δ) , x ≔ γ′ ⟨ x ⟩ + (p ·ᶜ δ′) ⟨ x ⟩
       ≡˘⟨ cong (_ , x ≔_) (lookup-distrib-+ᶜ γ′ (p ·ᶜ δ′) x) ⟩
    (γ +ᶜ p ·ᶜ δ) , x ≔ (γ′ +ᶜ p ·ᶜ δ′) ⟨ x ⟩ ∎

Conₘ-interchange
  (prodʷₘ {γ = γ} {p = p} {δ = δ} ▸t ▸u)
  (prodʷₘ {γ = γ′} {δ = δ′} ▸t′ ▸u′) x = subst
  (_▸[ _ ] _)
  (p ·ᶜ (γ , x ≔ γ′ ⟨ x ⟩) +ᶜ (δ , x ≔ δ′ ⟨ x ⟩)      ≡˘⟨ cong (_+ᶜ _) (update-distrib-·ᶜ _ _ _ _) ⟩
   (p ·ᶜ γ , x ≔ p · γ′ ⟨ x ⟩) +ᶜ (δ , x ≔ δ′ ⟨ x ⟩)  ≡˘⟨ update-distrib-+ᶜ _ _ _ _ _ ⟩
   p ·ᶜ γ +ᶜ δ , x ≔ p · γ′ ⟨ x ⟩ + δ′ ⟨ x ⟩          ≡˘⟨ cong (λ γ → _ , x ≔ γ + _) (lookup-distrib-·ᶜ γ′ _ _) ⟩
   p ·ᶜ γ +ᶜ δ , x ≔ (p ·ᶜ γ′) ⟨ x ⟩ + δ′ ⟨ x ⟩       ≡˘⟨ cong (_ , _ ≔_) (lookup-distrib-+ᶜ (_ ·ᶜ γ′) _ _) ⟩
   p ·ᶜ γ +ᶜ δ , x ≔ (p ·ᶜ γ′ +ᶜ δ′) ⟨ x ⟩            ∎)
  (prodʷₘ (Conₘ-interchange ▸t ▸t′ x) (Conₘ-interchange ▸u ▸u′ x))
  where
  open Tools.Reasoning.PropositionalEquality

Conₘ-interchange
  (prodˢₘ {γ = γ} {p = p} {δ = δ} ▸t ▸u)
  (prodˢₘ {γ = γ′} {δ = δ′} ▸t′ ▸u′) x = subst
  (_▸[ _ ] _)
  (p ·ᶜ (γ , x ≔ γ′ ⟨ x ⟩) ∧ᶜ (δ , x ≔ δ′ ⟨ x ⟩)      ≡˘⟨ cong (_∧ᶜ _) (update-distrib-·ᶜ _ _ _ _) ⟩
   (p ·ᶜ γ , x ≔ p · γ′ ⟨ x ⟩) ∧ᶜ (δ , x ≔ δ′ ⟨ x ⟩)  ≡˘⟨ update-distrib-∧ᶜ _ _ _ _ _ ⟩
   p ·ᶜ γ ∧ᶜ δ , x ≔ p · γ′ ⟨ x ⟩ ∧ δ′ ⟨ x ⟩          ≡˘⟨ cong (λ p → _ , x ≔ p ∧ _) (lookup-distrib-·ᶜ γ′ _ _) ⟩
   p ·ᶜ γ ∧ᶜ δ , x ≔ (p ·ᶜ γ′) ⟨ x ⟩ ∧ δ′ ⟨ x ⟩       ≡˘⟨ cong (_ , _ ≔_) (lookup-distrib-∧ᶜ (_ ·ᶜ γ′) _ _) ⟩
   p ·ᶜ γ ∧ᶜ δ , x ≔ (p ·ᶜ γ′ ∧ᶜ δ′) ⟨ x ⟩            ∎)
  (prodˢₘ (Conₘ-interchange ▸t ▸t′ x) (Conₘ-interchange ▸u ▸u′ x))
  where
  open Tools.Reasoning.PropositionalEquality

Conₘ-interchange (fstₘ m γ▸t PE.refl ok) (fstₘ _ δ▸t eq _) x =
  fstₘ m (Conₘ-interchange γ▸t (▸-cong eq δ▸t) x) PE.refl ok
Conₘ-interchange (sndₘ γ▸t) (sndₘ δ▸t) x =
  sndₘ (Conₘ-interchange γ▸t δ▸t x)

Conₘ-interchange
  (prodrecₘ {γ = γ} {r = r} {δ = δ} γ▸t δ▸t η▸A _)
  (prodrecₘ {γ = γ′} {δ = δ′} γ▸t₁ δ▸t₁ _ ok)
  x = subst (_▸[ _ ] _)
    (begin
       r ·ᶜ (γ , x ≔ γ′ ⟨ x ⟩) +ᶜ (δ , x ≔ δ′ ⟨ x ⟩)      ≡˘⟨ cong (_+ᶜ _) (update-distrib-·ᶜ _ _ _ _) ⟩
       (r ·ᶜ γ , x ≔ r · γ′ ⟨ x ⟩) +ᶜ (δ , x ≔ δ′ ⟨ x ⟩)  ≡˘⟨ update-distrib-+ᶜ _ _ _ _ _ ⟩
       r ·ᶜ γ +ᶜ δ , x ≔ r · γ′ ⟨ x ⟩ + δ′ ⟨ x ⟩          ≡˘⟨ cong (λ y → _ , _ ≔ y + _) (lookup-distrib-·ᶜ γ′ _ _) ⟩
       r ·ᶜ γ +ᶜ δ , x ≔ (r ·ᶜ γ′) ⟨ x ⟩ + δ′ ⟨ x ⟩       ≡˘⟨ cong (λ y → _ , _ ≔ y) (lookup-distrib-+ᶜ (_ ·ᶜ γ′) _ _) ⟩
       r ·ᶜ γ +ᶜ δ , x ≔ (r ·ᶜ γ′ +ᶜ δ′) ⟨ x ⟩            ∎)
    (prodrecₘ
       (Conₘ-interchange γ▸t γ▸t₁ x)
       (Conₘ-interchange δ▸t δ▸t₁ (x +2))
       η▸A
       ok)
  where
  open Tools.Reasoning.PropositionalEquality

Conₘ-interchange zeroₘ zeroₘ x           =
  subst (_▸[ _ ] _) (PE.sym (update-self 𝟘ᶜ x)) zeroₘ
Conₘ-interchange (sucₘ γ▸t) (sucₘ δ▸t) x =
  sucₘ (Conₘ-interchange γ▸t δ▸t x)

Conₘ-interchange
  (natrecₘ {γ = γ} {δ = δ} {p = p} {r = r} {η = η}
     ⦃ has-nr = nr₁ ⦄ γ▸z δ▸s η▸n θ▸A)
  (natrecₘ {γ = γ′} {δ = δ′} {η = η′}
     ⦃ has-nr = nr₂ ⦄ γ′▸z δ′▸s η′▸n _)
  x =
  case Dedicated-nr-propositional nr₁ nr₂ of λ {
    refl →
  flip (subst (_▸[ _ ] _))
    (natrecₘ
       (Conₘ-interchange γ▸z γ′▸z x)
       (Conₘ-interchange δ▸s δ′▸s (x +2))
       (Conₘ-interchange η▸n η′▸n x)
       θ▸A)
    (nrᶜ p r (γ , x ≔ γ′ ⟨ x ⟩) (δ , x ≔ δ′ ⟨ x ⟩) (η , x ≔ η′ ⟨ x ⟩)  ≡⟨ ≈ᶜ→≡ nrᶜ-,≔ ⟩
     nrᶜ p r γ δ η , x ≔ nr p r (γ′ ⟨ x ⟩) (δ′ ⟨ x ⟩) (η′ ⟨ x ⟩)       ≡˘⟨ cong (_ , _ ≔_) (nrᶜ-⟨⟩ γ′) ⟩
     nrᶜ p r γ δ η , x ≔ nrᶜ p r γ′ δ′ η′ ⟨ x ⟩                        ∎) }
  where
  open import Graded.Modality.Dedicated-nr.Instance
  open Tools.Reasoning.PropositionalEquality

Conₘ-interchange
  (natrec-no-nrₘ {γ = γ} {δ = δ} {p = p} {r = r} {η = η} {χ = χ}
     ⦃ no-nr = ¬nr ⦄ γ▸z δ▸s η▸n θ▸A χ≤γ χ≤δ χ≤η fix)
  (natrec-no-nrₘ {γ = γ′} {δ = δ′} {η = η′} {χ = χ′}
     γ′▸z δ′▸s η′▸n _ χ′≤γ′ χ′≤δ′ χ′≤η′ fix′)
  x =
  natrec-no-nrₘ ⦃ no-nr = ¬nr ⦄
    (Conₘ-interchange γ▸z γ′▸z x)
    (Conₘ-interchange δ▸s δ′▸s (x +2))
    (Conₘ-interchange η▸n η′▸n x)
    θ▸A
    (begin
       χ , x ≔ χ′ ⟨ x ⟩  ≤⟨ update-monotone _ χ≤γ (lookup-monotone _ χ′≤γ′) ⟩
       γ , x ≔ γ′ ⟨ x ⟩  ∎)
    (λ ok → begin
       χ , x ≔ χ′ ⟨ x ⟩  ≤⟨ update-monotone _ (χ≤δ ok) (lookup-monotone _ (χ′≤δ′ ok)) ⟩
       δ , x ≔ δ′ ⟨ x ⟩  ∎)
    (begin
       χ , x ≔ χ′ ⟨ x ⟩  ≤⟨ update-monotone _ χ≤η (lookup-monotone _ χ′≤η′) ⟩
       η , x ≔ η′ ⟨ x ⟩  ∎)
    (begin
       χ , x ≔ χ′ ⟨ x ⟩                                              ≤⟨ update-monotone _ fix (lookup-monotone _ fix′) ⟩

       δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ χ , x ≔ (δ′ +ᶜ p ·ᶜ η′ +ᶜ r ·ᶜ χ′) ⟨ x ⟩  ≈⟨ update-congʳ $
                                                                        trans (lookup-distrib-+ᶜ δ′ _ _) $
                                                                        cong (_ +_) $
                                                                        trans (lookup-distrib-+ᶜ (_ ·ᶜ η′) _ _) $
                                                                        cong₂ _+_
                                                                          (lookup-distrib-·ᶜ η′ _ _)
                                                                          (lookup-distrib-·ᶜ χ′ _ _) ⟩
       δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ χ ,
       x ≔ δ′ ⟨ x ⟩ + p · η′ ⟨ x ⟩ + r · χ′ ⟨ x ⟩                    ≡⟨ trans (update-distrib-+ᶜ _ _ _ _ _) $
                                                                        cong (_ +ᶜ_) $
                                                                        trans (update-distrib-+ᶜ _ _ _ _ _) $
                                                                        cong₂ _+ᶜ_
                                                                          (update-distrib-·ᶜ _ _ _ _)
                                                                          (update-distrib-·ᶜ _ _ _ _) ⟩
       (δ , x ≔ δ′ ⟨ x ⟩) +ᶜ
       p ·ᶜ (η , x ≔ η′ ⟨ x ⟩) +ᶜ r ·ᶜ (χ , x ≔ χ′ ⟨ x ⟩)            ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

Conₘ-interchange (natrecₘ _ _ _ _) (natrec-no-nrₘ _ _ _ _ _ _ _ _) _ =
  ⊥-elim not-nr-and-no-nr

Conₘ-interchange (natrec-no-nrₘ _ _ _ _ _ _ _ _) (natrecₘ _ _ _ _) _ =
  ⊥-elim not-nr-and-no-nr

Conₘ-interchange
  (emptyrecₘ {γ = γ} {m = m} {p = p} γ▸t η▸A)
  (emptyrecₘ {γ = δ} δ▸t _)
  x =
  subst (_▸[ _ ] _)
    (begin
       p ·ᶜ (γ , x ≔ δ ⟨ x ⟩)       ≡˘⟨ update-distrib-·ᶜ _ _ _ _ ⟩
       p ·ᶜ γ , x ≔ p · (δ ⟨ x ⟩)   ≡˘⟨ cong (_ , _ ≔_) (lookup-distrib-·ᶜ δ _ _) ⟩
       p ·ᶜ γ , x ≔ (p ·ᶜ δ) ⟨ x ⟩  ∎)
    (emptyrecₘ (Conₘ-interchange γ▸t δ▸t x) η▸A)
  where
  open Tools.Reasoning.PropositionalEquality

Conₘ-interchange starʷₘ starʷₘ x =
  subst (_▸[ _ ] _) (PE.sym (update-self 𝟘ᶜ x)) starₘ

Conₘ-interchange (starˢₘ {γ = γ} {m = m} prop) (starˢₘ {γ = δ} prop′) x =
  sub (starˢₘ prop″)
      (≤ᶜ-reflexive eq)
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid
  eq = begin
    ⌜ m ⌝ ·ᶜ γ , x ≔ (⌜ m ⌝ ·ᶜ δ) ⟨ x ⟩  ≡⟨ cong (_ , _ ≔_) (lookup-distrib-·ᶜ δ ⌜ m ⌝ x) ⟩
    ⌜ m ⌝ ·ᶜ γ , x ≔ (⌜ m ⌝ · δ ⟨ x ⟩)   ≡⟨ update-distrib-·ᶜ γ ⌜ m ⌝ (δ ⟨ x ⟩) x ⟩
    ⌜ m ⌝ ·ᶜ (γ , x ≔ δ ⟨ x ⟩)           ∎
  prop″ = λ ¬sink → begin
    𝟘ᶜ                ≡˘⟨ 𝟘ᶜ,≔𝟘 ⟩
    𝟘ᶜ , x ≔ 𝟘        ≡˘⟨ cong (𝟘ᶜ , x ≔_) (𝟘ᶜ-lookup x) ⟩
    𝟘ᶜ , x ≔ 𝟘ᶜ ⟨ x ⟩  ≈⟨ update-cong (prop ¬sink) (lookup-cong (prop′ ¬sink)) ⟩
    γ , x ≔ δ ⟨ x ⟩    ∎


Conₘ-interchange (unitrecₘ {γ = γ} {p = p} {δ = δ} γ▸t δ▸u η▸A ok)
                 (unitrecₘ {γ = γ′} {δ = δ′} γ′▸t δ′▸u _ _) x =
  subst (_▸[ _ ] _)
    (begin
       p ·ᶜ (γ , x ≔ γ′ ⟨ x ⟩) +ᶜ (δ , x ≔ δ′ ⟨ x ⟩)      ≡˘⟨ cong (_+ᶜ _) (update-distrib-·ᶜ γ p (γ′ ⟨ x ⟩) x) ⟩
       (p ·ᶜ γ , x ≔ p · γ′ ⟨ x ⟩) +ᶜ (δ , x ≔ δ′ ⟨ x ⟩)  ≡˘⟨ update-distrib-+ᶜ (p ·ᶜ γ) δ (p · γ′ ⟨ x ⟩) (δ′ ⟨ x ⟩) x ⟩
       p ·ᶜ γ +ᶜ δ , x ≔ p · γ′ ⟨ x ⟩ + δ′ ⟨ x ⟩          ≡˘⟨ cong (p ·ᶜ γ +ᶜ δ , x ≔_) (cong (_+ _) (lookup-distrib-·ᶜ γ′ p x)) ⟩
       p ·ᶜ γ +ᶜ δ , x ≔ (p ·ᶜ γ′) ⟨ x ⟩ + δ′ ⟨ x ⟩       ≡˘⟨ cong (_ , x ≔_) (lookup-distrib-+ᶜ (p ·ᶜ γ′) δ′ x) ⟩
       p ·ᶜ γ +ᶜ δ , x ≔ (p ·ᶜ γ′ +ᶜ δ′) ⟨ x ⟩           ∎)
    (unitrecₘ (Conₘ-interchange γ▸t γ′▸t x)
              (Conₘ-interchange δ▸u δ′▸u x) η▸A ok)
  where
  open Tools.Reasoning.PropositionalEquality

Conₘ-interchange
  (Idₘ {δ = δ} {η = η} ok ▸A ▸t ▸u)
  (Idₘ {δ = δ′} {η = η′} _ _ ▸t′ ▸u′) x =
  subst (_▸[ _ ] _)
    (begin
       (δ , x ≔ δ′ ⟨ x ⟩) +ᶜ (η , x ≔ η′ ⟨ x ⟩)  ≡˘⟨ update-distrib-+ᶜ δ _ _ _ x ⟩
       δ +ᶜ η , x ≔ δ′ ⟨ x ⟩ + η′ ⟨ x ⟩          ≡˘⟨ cong (_ , x ≔_) (lookup-distrib-+ᶜ δ′ _ _) ⟩
       δ +ᶜ η , x ≔ (δ′ +ᶜ η′) ⟨ x ⟩             ∎)
    (Idₘ ok ▸A (Conₘ-interchange ▸t ▸t′ x) (Conₘ-interchange ▸u ▸u′ x))
    where
  open Tools.Reasoning.PropositionalEquality

Conₘ-interchange (Id₀ₘ ok ▸A ▸t ▸u) (Id₀ₘ _ _ _ _) x =
  subst (_▸[ _ ] _)
    (begin
       𝟘ᶜ                 ≡˘⟨ update-self _ _ ⟩
       𝟘ᶜ , x ≔ 𝟘ᶜ ⟨ x ⟩  ∎)
    (Id₀ₘ ok ▸A ▸t ▸u)
  where
  open Tools.Reasoning.PropositionalEquality

Conₘ-interchange (Idₘ not-ok _ _ _) (Id₀ₘ ok _ _ _) =
  ⊥-elim (not-ok ok)

Conₘ-interchange (Id₀ₘ ok _ _ _) (Idₘ not-ok _ _ _) =
  ⊥-elim (not-ok ok)

Conₘ-interchange rflₘ rflₘ x =
  subst (_▸[ _ ] _) (PE.sym (update-self 𝟘ᶜ x)) rflₘ

Conₘ-interchange
  (Jₘ {γ₂} {γ₃} {γ₄} {γ₅} {γ₆} ok ▸A ▸t₁ ▸F₁ ▸u₁ ▸v₁ ▸w₁)
  (Jₘ {γ₂ = δ₂} {γ₃ = δ₃} {γ₄ = δ₄} {γ₅ = δ₅} {γ₆ = δ₆}
     _ _ ▸t₂ ▸F₂ ▸u₂ ▸v₂ ▸w₂)
  x =
  subst (_▸[ _ ] _)
    (begin
       ω ·ᶜ
       ((γ₂ , x ≔ δ₂ ⟨ x ⟩) ∧ᶜ (γ₃ , x ≔ δ₃ ⟨ x ⟩) ∧ᶜ
        (γ₄ , x ≔ δ₄ ⟨ x ⟩) ∧ᶜ (γ₅ , x ≔ δ₅ ⟨ x ⟩) ∧ᶜ
        (γ₆ , x ≔ δ₆ ⟨ x ⟩))                           ≡˘⟨ cong (ω ·ᶜ_) $
                                                           trans (cong (_ , _ ≔_) $ lookup-distrib-∧ᶜ δ₂ _ _) $
                                                           trans (update-distrib-∧ᶜ _ _ _ _ _) $
                                                           cong (_ ∧ᶜ_) $
                                                           trans (cong (_ , _ ≔_) $ lookup-distrib-∧ᶜ δ₃ _ _) $
                                                           trans (update-distrib-∧ᶜ _ _ _ _ _) $
                                                           cong (_ ∧ᶜ_) $
                                                           trans (cong (_ , _ ≔_) $ lookup-distrib-∧ᶜ δ₄ _ _) $
                                                           trans (update-distrib-∧ᶜ _ _ _ _ _) $
                                                           cong (_ ∧ᶜ_) $
                                                           trans (cong (_ , _ ≔_) $ lookup-distrib-∧ᶜ δ₅ _ _) $
                                                           update-distrib-∧ᶜ _ _ _ _ _ ⟩
       ω ·ᶜ
       (γ₂ ∧ᶜ γ₃ ∧ᶜ γ₄ ∧ᶜ γ₅ ∧ᶜ γ₆ ,
        x ≔ (δ₂ ∧ᶜ δ₃ ∧ᶜ δ₄ ∧ᶜ δ₅ ∧ᶜ δ₆) ⟨ x ⟩)        ≡˘⟨ update-distrib-·ᶜ _ _ _ _ ⟩


       ω ·ᶜ (γ₂ ∧ᶜ γ₃ ∧ᶜ γ₄ ∧ᶜ γ₅ ∧ᶜ γ₆) ,
       x ≔ ω · (δ₂ ∧ᶜ δ₃ ∧ᶜ δ₄ ∧ᶜ δ₅ ∧ᶜ δ₆) ⟨ x ⟩      ≡˘⟨ cong (_ , _ ≔_) $ lookup-distrib-·ᶜ (δ₂ ∧ᶜ _) _ _ ⟩

       ω ·ᶜ (γ₂ ∧ᶜ γ₃ ∧ᶜ γ₄ ∧ᶜ γ₅ ∧ᶜ γ₆) ,
       x ≔ (ω ·ᶜ (δ₂ ∧ᶜ δ₃ ∧ᶜ δ₄ ∧ᶜ δ₅ ∧ᶜ δ₆)) ⟨ x ⟩   ∎)
    (Jₘ ok ▸A
       (Conₘ-interchange ▸t₁ ▸t₂ x)
       (Conₘ-interchange ▸F₁ ▸F₂ (x +2))
       (Conₘ-interchange ▸u₁ ▸u₂ x)
       (Conₘ-interchange ▸v₁ ▸v₂ x)
       (Conₘ-interchange ▸w₁ ▸w₂ x))
  where
  open Tools.Reasoning.PropositionalEquality

Conₘ-interchange
  (J₀ₘ ok ▸A ▸t₁ ▸F₁ ▸u₁ ▸v₁ ▸w₁)
  (J₀ₘ _ _ _ _ ▸u₂ _ _)
  x =
  J₀ₘ ok ▸A ▸t₁ ▸F₁ (Conₘ-interchange ▸u₁ ▸u₂ x) ▸v₁ ▸w₁

Conₘ-interchange (Jₘ not-ok _ _ _ _ _ _) (J₀ₘ ok _ _ _ _ _ _) =
  ⊥-elim (not-ok ok)

Conₘ-interchange (J₀ₘ ok _ _ _ _ _ _) (Jₘ not-ok _ _ _ _ _ _) =
  ⊥-elim (not-ok ok)

Conₘ-interchange
  (Kₘ {γ₂} {γ₃} {γ₄} {γ₅} ok ▸A ▸t₁ ▸F₁ ▸u₁ ▸v₁)
  (Kₘ {γ₂ = δ₂} {γ₃ = δ₃} {γ₄ = δ₄} {γ₅ = δ₅}
     _ _ ▸t₂ ▸F₂ ▸u₂ ▸v₂)
  x =
  subst (_▸[ _ ] _)
    (begin
       ω ·ᶜ
       ((γ₂ , x ≔ δ₂ ⟨ x ⟩) ∧ᶜ (γ₃ , x ≔ δ₃ ⟨ x ⟩) ∧ᶜ
        (γ₄ , x ≔ δ₄ ⟨ x ⟩) ∧ᶜ (γ₅ , x ≔ δ₅ ⟨ x ⟩))    ≡˘⟨ cong (ω ·ᶜ_) $
                                                           trans (cong (_ , _ ≔_) $ lookup-distrib-∧ᶜ δ₂ _ _) $
                                                           trans (update-distrib-∧ᶜ _ _ _ _ _) $
                                                           cong (_ ∧ᶜ_) $
                                                           trans (cong (_ , _ ≔_) $ lookup-distrib-∧ᶜ δ₃ _ _) $
                                                           trans (update-distrib-∧ᶜ _ _ _ _ _) $
                                                           cong (_ ∧ᶜ_) $
                                                           trans (cong (_ , _ ≔_) $ lookup-distrib-∧ᶜ δ₄ _ _) $
                                                           update-distrib-∧ᶜ _ _ _ _ _ ⟩
       ω ·ᶜ
       (γ₂ ∧ᶜ γ₃ ∧ᶜ γ₄ ∧ᶜ γ₅ ,
        x ≔ (δ₂ ∧ᶜ δ₃ ∧ᶜ δ₄ ∧ᶜ δ₅) ⟨ x ⟩)              ≡˘⟨ update-distrib-·ᶜ _ _ _ _ ⟩


       ω ·ᶜ (γ₂ ∧ᶜ γ₃ ∧ᶜ γ₄ ∧ᶜ γ₅) ,
       x ≔ ω · (δ₂ ∧ᶜ δ₃ ∧ᶜ δ₄ ∧ᶜ δ₅) ⟨ x ⟩            ≡˘⟨ cong (_ , _ ≔_) $ lookup-distrib-·ᶜ (δ₂ ∧ᶜ _) _ _ ⟩

       ω ·ᶜ (γ₂ ∧ᶜ γ₃ ∧ᶜ γ₄ ∧ᶜ γ₅) ,
       x ≔ (ω ·ᶜ (δ₂ ∧ᶜ δ₃ ∧ᶜ δ₄ ∧ᶜ δ₅)) ⟨ x ⟩         ∎)
    (Kₘ ok ▸A
       (Conₘ-interchange ▸t₁ ▸t₂ x)
       (Conₘ-interchange ▸F₁ ▸F₂ (x +1))
       (Conₘ-interchange ▸u₁ ▸u₂ x)
       (Conₘ-interchange ▸v₁ ▸v₂ x))
  where
  open Tools.Reasoning.PropositionalEquality

Conₘ-interchange (K₀ₘ ok ▸A ▸t₁ ▸F₁ ▸u₁ ▸v₁) (K₀ₘ _ _ _ _ ▸u₂ _) x =
  K₀ₘ ok ▸A ▸t₁ ▸F₁ (Conₘ-interchange ▸u₁ ▸u₂ x) ▸v₁

Conₘ-interchange (Kₘ not-ok _ _ _ _ _) (K₀ₘ ok _ _ _ _ _) =
  ⊥-elim (not-ok ok)

Conₘ-interchange (K₀ₘ ok _ _ _ _ _) (Kₘ not-ok _ _ _ _ _) =
  ⊥-elim (not-ok ok)

Conₘ-interchange ([]-congₘ ▸A₁ ▸t₁ ▸u₁ ▸v₁) ([]-congₘ _ _ _ _) x =
  subst (_▸[ _ ] _)
    (PE.sym (update-self 𝟘ᶜ x))
    ([]-congₘ ▸A₁ ▸t₁ ▸u₁ ▸v₁)

-- Some variants of Conₘ-interchange

Conₘ-interchange₁ : γ ▸[ m ] t → δ ▸[ m ] t
                  → tailₘ γ ∙ δ ⟨ x0 ⟩ ▸[ m ] t
Conₘ-interchange₁ {γ = γ} {m} {t} {δ} γ▸t δ▸t =
  subst (_▸[ m ] t) (update-head γ (δ ⟨ x0 ⟩))
        (Conₘ-interchange γ▸t δ▸t x0)


Conₘ-interchange₂ : γ ▸[ m ] t → δ ▸[ m ] t
                  → tailₘ (tailₘ γ) ∙ δ ⟨ x1 ⟩ ∙ δ ⟨ x0 ⟩ ▸[ m ] t
Conₘ-interchange₂ {γ = γ} {m} {t} {δ} γ▸t δ▸t =
  subst (_▸[ m ] t) eq
        (Conₘ-interchange (Conₘ-interchange γ▸t δ▸t x1) δ▸t x0)
  where
  open Tools.Reasoning.PropositionalEquality
  δ₁ = δ ⟨ x1 ⟩
  δ₀ = δ ⟨ x0 ⟩
  eq = begin
    γ , x1 ≔ δ₁ , x0 ≔ δ₀ ≡⟨ update-head _ _ ⟩
    tailₘ (γ , x1 ≔ δ₁) ∙ δ₀ ≡⟨ cong (λ x → tailₘ x ∙ δ₀) (update-step γ δ₁ x0) ⟩
    (tailₘ γ , x0 ≔ δ₁) ∙ δ₀ ≡⟨ cong (_∙ _) (update-head (tailₘ γ) δ₁) ⟩
    tailₘ (tailₘ γ) ∙ δ₁ ∙ δ₀ ∎


------------------------------------------------------------------------
-- Variants of some usage rules

module _ where

  open import Graded.Modality.Dedicated-nr.Instance

  -- A variant of natrecₘ and natrec-no-nrₘ.

  natrec-nr-or-no-nrₘ :
    γ ▸[ m ] t →
    δ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · r ▸[ m ] u →
    η ▸[ m ] v →
    θ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] A →
    (⦃ has-nr : Dedicated-nr ⦄ →
     χ ≤ᶜ nrᶜ p r γ δ η) →
    (⦃ no-nr : No-dedicated-nr ⦄ →
     χ ≤ᶜ γ ×
     (T 𝟘ᵐ-allowed →
      χ ≤ᶜ δ) ×
     (⦃ 𝟘-well-behaved : Has-well-behaved-zero semiring-with-meet ⦄ →
      χ ≤ᶜ η) ×
     χ ≤ᶜ δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ χ) →
    χ ▸[ m ] natrec p q r A t u v
  natrec-nr-or-no-nrₘ ▸t ▸u ▸v ▸A hyp₁ hyp₂ =
    case dedicated-nr? of λ where
      does-have-nr →
        sub (natrecₘ ▸t ▸u ▸v ▸A) hyp₁
      does-not-have-nr →
        case hyp₂ of λ {
          (χ≤γ , χ≤δ , χ≤η , fix) →
        natrec-no-nrₘ ▸t ▸u ▸v ▸A χ≤γ χ≤δ χ≤η fix }

opaque

  -- A variant of Idₘ and Id₀ₘ.

  Idₘ′ :
    γ₁ ▸[ 𝟘ᵐ? ] A →
    γ₂ ▸[ m ] t →
    γ₃ ▸[ m ] u →
    δ ≤ᶜ 𝟘ᶜ →
    δ ≤ᶜ γ₂ +ᶜ γ₃ →
    δ ▸[ m ] Id A t u
  Idₘ′ {γ₂} {m} {γ₃} {δ} ▸A ▸t ▸u δ≤𝟘ᶜ δ≤γ₂+γ₃ =
    case Id-erased? of λ where
      (no not-erased) → sub (Idₘ not-erased ▸A ▸t ▸u) δ≤γ₂+γ₃
      (yes erased)    → 𝟘ᵐ-allowed-elim
        (λ ok →
           sub (Id₀ₘ erased ▸A (𝟘ᶜ▸[𝟘ᵐ?] ok ▸t) (𝟘ᶜ▸[𝟘ᵐ?] ok ▸u)) δ≤𝟘ᶜ)
        (λ not-ok →
           sub
             (Id₀ₘ erased ▸A (▸-without-𝟘ᵐ not-ok ▸t)
                (▸-without-𝟘ᵐ not-ok ▸u))
             δ≤𝟘ᶜ)

opaque

  -- A variant of Jₘ and J₀ₘ.

  Jₘ′ :
    γ₁ ▸[ 𝟘ᵐ? ] A →
    γ₂ ▸[ m ] t →
    γ₃ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · q ▸[ m ] B →
    γ₄ ▸[ m ] u →
    γ₅ ▸[ m ] v →
    γ₆ ▸[ m ] w →
    δ ≤ᶜ ω ·ᶜ (γ₂ ∧ᶜ γ₃ ∧ᶜ γ₄ ∧ᶜ γ₅ ∧ᶜ γ₆) →
    δ ▸[ m ] J p q A t B u v w
  Jₘ′ {γ₂} {m} {γ₃} {p} {q} {γ₄} {γ₅} {γ₆} {δ} ▸A ▸t ▸B ▸u ▸v ▸w δ≤ =
    case Erased-matches-for-J? m of λ where
      (no not-erased) →
        sub (Jₘ not-erased ▸A ▸t ▸B ▸u ▸v ▸w) δ≤
      (yes erased) → 𝟘ᵐ-allowed-elim
        (λ ok →
           sub
             (J₀ₘ erased ▸A (𝟘ᶜ▸[𝟘ᵐ?] ok ▸t)
                (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
                 sub (𝟘ᶜ▸[𝟘ᵐ?] ok ▸B) $ begin
                   𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · p ∙ ⌜ 𝟘ᵐ? ⌝ · q  ≈⟨ ≈ᶜ-refl ∙
                                                      cong (λ m → ⌜ m ⌝ · p) (𝟘ᵐ?≡𝟘ᵐ {ok = ok}) ∙
                                                      cong (λ m → ⌜ m ⌝ · q) (𝟘ᵐ?≡𝟘ᵐ {ok = ok}) ⟩
                   𝟘ᶜ ∙ 𝟘 · p ∙ 𝟘 · q              ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ∙ ·-zeroˡ _ ⟩
                   𝟘ᶜ                              ∎)
                ▸u (𝟘ᶜ▸[𝟘ᵐ?] ok ▸v) (𝟘ᶜ▸[𝟘ᵐ?] ok ▸w))
             δ≤γ₄)
        (λ not-ok →
           sub
             (J₀ₘ erased ▸A (▸-without-𝟘ᵐ not-ok ▸t)
                (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
                 sub (▸-without-𝟘ᵐ not-ok ▸B) $ begin
                   γ₃ ∙ ⌜ 𝟘ᵐ? ⌝ · p ∙ ⌜ 𝟘ᵐ? ⌝ · q  ≈⟨ ≈ᶜ-refl ∙
                                                      cong (λ m → ⌜ m ⌝ · p) (Mode-propositional-without-𝟘ᵐ {m₁ = 𝟘ᵐ?} {m₂ = m} not-ok) ∙
                                                      cong (λ m → ⌜ m ⌝ · q) (Mode-propositional-without-𝟘ᵐ {m₁ = 𝟘ᵐ?} {m₂ = m} not-ok) ⟩
                   γ₃ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · q      ∎)
                ▸u (▸-without-𝟘ᵐ not-ok ▸v) (▸-without-𝟘ᵐ not-ok ▸w))
             δ≤γ₄)
    where
    δ≤γ₄ : δ ≤ᶜ γ₄
    δ≤γ₄ = begin
      δ                                  ≤⟨ δ≤ ⟩
      ω ·ᶜ (γ₂ ∧ᶜ γ₃ ∧ᶜ γ₄ ∧ᶜ γ₅ ∧ᶜ γ₆)  ≤⟨ ω·ᶜ-decreasing ⟩
      γ₂ ∧ᶜ γ₃ ∧ᶜ γ₄ ∧ᶜ γ₅ ∧ᶜ γ₆         ≤⟨ ≤ᶜ-trans (∧ᶜ-decreasingʳ _ _) $
                                            ≤ᶜ-trans (∧ᶜ-decreasingʳ _ _) $
                                            ∧ᶜ-decreasingˡ _ _ ⟩
      γ₄                                 ∎
      where
      open Tools.Reasoning.PartialOrder ≤ᶜ-poset

opaque

  -- A variant of Kₘ and K₀ₘ.

  Kₘ′ :
    γ₁ ▸[ 𝟘ᵐ? ] A →
    γ₂ ▸[ m ] t →
    γ₃ ∙ ⌜ m ⌝ · p ▸[ m ] B →
    γ₄ ▸[ m ] u →
    γ₅ ▸[ m ] v →
    δ ≤ᶜ ω ·ᶜ (γ₂ ∧ᶜ γ₃ ∧ᶜ γ₄ ∧ᶜ γ₅) →
    δ ▸[ m ] K p A t B u v
  Kₘ′ {γ₂} {m} {γ₃} {p} {γ₄} {γ₅} {δ} ▸A ▸t ▸B ▸u ▸v δ≤ =
    case Erased-matches-for-K? m of λ where
      (no not-erased) →
        sub (Kₘ not-erased ▸A ▸t ▸B ▸u ▸v) δ≤
      (yes erased) → 𝟘ᵐ-allowed-elim
        (λ ok →
           sub
             (K₀ₘ erased ▸A (𝟘ᶜ▸[𝟘ᵐ?] ok ▸t)
                (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
                 sub (𝟘ᶜ▸[𝟘ᵐ?] ok ▸B) $ begin
                   𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · p  ≈⟨ ≈ᶜ-refl ∙ cong (λ m → ⌜ m ⌝ · p) (𝟘ᵐ?≡𝟘ᵐ {ok = ok}) ⟩
                   𝟘ᶜ ∙ 𝟘 · p        ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
                   𝟘ᶜ                ∎)
                ▸u (𝟘ᶜ▸[𝟘ᵐ?] ok ▸v))
             δ≤γ₄)
        (λ not-ok →
           sub
             (K₀ₘ erased ▸A (▸-without-𝟘ᵐ not-ok ▸t)
                (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
                 sub (▸-without-𝟘ᵐ not-ok ▸B) $ begin
                   γ₃ ∙ ⌜ 𝟘ᵐ? ⌝ · p  ≈⟨ ≈ᶜ-refl ∙ cong (λ m → ⌜ m ⌝ · p) (Mode-propositional-without-𝟘ᵐ {m₁ = 𝟘ᵐ?} {m₂ = m} not-ok) ⟩
                   γ₃ ∙ ⌜ m ⌝ · p    ∎)
                ▸u (▸-without-𝟘ᵐ not-ok ▸v))
             δ≤γ₄)
    where
    δ≤γ₄ : δ ≤ᶜ γ₄
    δ≤γ₄ = begin
      δ                            ≤⟨ δ≤ ⟩
      ω ·ᶜ (γ₂ ∧ᶜ γ₃ ∧ᶜ γ₄ ∧ᶜ γ₅)  ≤⟨ ω·ᶜ-decreasing ⟩
      γ₂ ∧ᶜ γ₃ ∧ᶜ γ₄ ∧ᶜ γ₅         ≤⟨ ≤ᶜ-trans (∧ᶜ-decreasingʳ _ _) $
                                      ≤ᶜ-trans (∧ᶜ-decreasingʳ _ _) $
                                      ∧ᶜ-decreasingˡ _ _ ⟩
      γ₄                           ∎
      where
      open Tools.Reasoning.PartialOrder ≤ᶜ-poset

------------------------------------------------------------------------
-- Lemmas related to ⌈_⌉

-- The context ⌈ t ⌉ 𝟘ᵐ[ ok ] is equivalent to 𝟘ᶜ.

⌈⌉-𝟘ᵐ :
  ⦃ has-nr : Has-nr semiring-with-meet ⦄ →
  (t : Term n) → ⌈ t ⌉ 𝟘ᵐ[ ok ] ≈ᶜ 𝟘ᶜ
⌈⌉-𝟘ᵐ (var x) = begin
  𝟘ᶜ , x ≔ 𝟘  ≡⟨ 𝟘ᶜ,≔𝟘 ⟩
  𝟘ᶜ          ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid
⌈⌉-𝟘ᵐ U =
  ≈ᶜ-refl
⌈⌉-𝟘ᵐ {ok = ok} (ΠΣ⟨ _ ⟩ _ , _ ▷ F ▹ G) = begin
  (⌈ F ⌉ 𝟘ᵐ[ ok ] +ᶜ tailₘ (⌈ G ⌉ 𝟘ᵐ[ ok ]))  ≈⟨ +ᶜ-cong (⌈⌉-𝟘ᵐ F) (tailₘ-cong (⌈⌉-𝟘ᵐ G)) ⟩
  𝟘ᶜ +ᶜ 𝟘ᶜ                                    ≈⟨ +ᶜ-identityʳ _ ⟩
  𝟘ᶜ                                          ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid
⌈⌉-𝟘ᵐ (lam _ t) =
  tailₘ-cong (⌈⌉-𝟘ᵐ t)
⌈⌉-𝟘ᵐ {ok = ok} (t ∘⟨ p ⟩ u) = begin
  ⌈ t ⌉ 𝟘ᵐ[ ok ] +ᶜ p ·ᶜ ⌈ u ⌉ 𝟘ᵐ[ ok ]  ≈⟨ +ᶜ-cong (⌈⌉-𝟘ᵐ t) (·ᶜ-congˡ (⌈⌉-𝟘ᵐ u)) ⟩
  𝟘ᶜ +ᶜ p ·ᶜ 𝟘ᶜ                          ≈⟨ +ᶜ-congˡ (·ᶜ-zeroʳ _) ⟩
  𝟘ᶜ +ᶜ 𝟘ᶜ                               ≈⟨ +ᶜ-identityˡ _ ⟩
  𝟘ᶜ                                     ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid
⌈⌉-𝟘ᵐ {ok = ok} (prod 𝕨 p t u) = begin
  p ·ᶜ ⌈ t ⌉ 𝟘ᵐ[ ok ] +ᶜ ⌈ u ⌉ 𝟘ᵐ[ ok ]  ≈⟨ +ᶜ-cong (·ᶜ-congˡ (⌈⌉-𝟘ᵐ t)) (⌈⌉-𝟘ᵐ u) ⟩
  p ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ                          ≈⟨ +ᶜ-identityʳ _ ⟩
  p ·ᶜ 𝟘ᶜ                                ≈⟨ ·ᶜ-zeroʳ _ ⟩
  𝟘ᶜ                                     ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid
⌈⌉-𝟘ᵐ {ok = ok} (prod 𝕤 p t u) = begin
  p ·ᶜ ⌈ t ⌉ 𝟘ᵐ[ ok ] ∧ᶜ ⌈ u ⌉ 𝟘ᵐ[ ok ]  ≈⟨ ∧ᶜ-cong (·ᶜ-congˡ (⌈⌉-𝟘ᵐ t)) (⌈⌉-𝟘ᵐ u) ⟩
  p ·ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ                          ≈⟨ ∧ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
  𝟘ᶜ ∧ᶜ 𝟘ᶜ                               ≈⟨ ∧ᶜ-idem _ ⟩
  𝟘ᶜ                                     ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid
⌈⌉-𝟘ᵐ (fst _ t) =
  ⌈⌉-𝟘ᵐ t
⌈⌉-𝟘ᵐ (snd _ t) =
  ⌈⌉-𝟘ᵐ t
⌈⌉-𝟘ᵐ {ok = ok} (prodrec r _ _ _ t u) = begin
  r ·ᶜ ⌈ t ⌉ 𝟘ᵐ[ ok ] +ᶜ tailₘ (tailₘ (⌈ u ⌉ 𝟘ᵐ[ ok ]))  ≈⟨ +ᶜ-cong (·ᶜ-congˡ (⌈⌉-𝟘ᵐ t)) (tailₘ-cong (tailₘ-cong (⌈⌉-𝟘ᵐ u))) ⟩
  r ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ                                          ≈⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
  𝟘ᶜ +ᶜ 𝟘ᶜ                                               ≈⟨ +ᶜ-identityˡ _ ⟩
  𝟘ᶜ                                                     ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid
⌈⌉-𝟘ᵐ {ok = ok} (unitrec p q A t u) = begin
  p ·ᶜ ⌈ t ⌉ 𝟘ᵐ[ ok ] +ᶜ ⌈ u ⌉ 𝟘ᵐ[ ok ]  ≈⟨ +ᶜ-cong (·ᶜ-congˡ (⌈⌉-𝟘ᵐ t)) (⌈⌉-𝟘ᵐ u) ⟩
  p ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ                          ≈⟨ +ᶜ-identityʳ _ ⟩
  p ·ᶜ 𝟘ᶜ                                ≈⟨ ·ᶜ-zeroʳ _ ⟩
  𝟘ᶜ                                     ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid
⌈⌉-𝟘ᵐ ℕ =
  ≈ᶜ-refl
⌈⌉-𝟘ᵐ zero =
  ≈ᶜ-refl
⌈⌉-𝟘ᵐ (suc t) =
  ⌈⌉-𝟘ᵐ t
⌈⌉-𝟘ᵐ {ok = ok} (natrec p _ r A z s n) = begin
  nrᶜ p r (⌈ z ⌉ 𝟘ᵐ[ ok ]) (tailₘ (tailₘ (⌈ s ⌉ 𝟘ᵐ[ ok ])))
    (⌈ n ⌉ 𝟘ᵐ[ ok ])                                         ≈⟨ nrᶜ-cong (⌈⌉-𝟘ᵐ z) (tailₘ-cong (tailₘ-cong (⌈⌉-𝟘ᵐ s))) (⌈⌉-𝟘ᵐ n) ⟩

  nrᶜ p r 𝟘ᶜ 𝟘ᶜ 𝟘ᶜ                                           ≈⟨ nrᶜ-𝟘ᶜ ⟩

  𝟘ᶜ                                                         ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid
⌈⌉-𝟘ᵐ Unit! =
  ≈ᶜ-refl
⌈⌉-𝟘ᵐ star! = ≈ᶜ-refl
⌈⌉-𝟘ᵐ Empty =
  ≈ᶜ-refl
⌈⌉-𝟘ᵐ {ok = ok} (emptyrec p _ t) = begin
  p ·ᶜ ⌈ t ⌉ 𝟘ᵐ[ ok ]  ≈⟨ ·ᶜ-congˡ (⌈⌉-𝟘ᵐ t) ⟩
  p ·ᶜ 𝟘ᶜ              ≈⟨ ·ᶜ-zeroʳ _ ⟩
  𝟘ᶜ                   ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid
⌈⌉-𝟘ᵐ {ok = ok} (Id _ t u) with Id-erased?
… | yes _ = ≈ᶜ-refl
… | no _  = begin
  ⌈ t ⌉ 𝟘ᵐ[ ok ] +ᶜ ⌈ u ⌉ 𝟘ᵐ[ ok ]  ≈⟨ +ᶜ-cong (⌈⌉-𝟘ᵐ t) (⌈⌉-𝟘ᵐ u) ⟩
  𝟘ᶜ +ᶜ 𝟘ᶜ                          ≈⟨ +ᶜ-identityˡ _ ⟩
  𝟘ᶜ                                ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid
⌈⌉-𝟘ᵐ rfl =
  ≈ᶜ-refl
⌈⌉-𝟘ᵐ {ok} (J _ _ _ t B u v w) with Erased-matches-for-J? 𝟘ᵐ[ ok ]
… | yes _ = ⌈⌉-𝟘ᵐ u
… | no _  = begin
  ω ·ᶜ
  (⌈ t ⌉ 𝟘ᵐ[ ok ] ∧ᶜ tailₘ (tailₘ (⌈ B ⌉ 𝟘ᵐ[ ok ])) ∧ᶜ ⌈ u ⌉ 𝟘ᵐ[ ok ] ∧ᶜ
   ⌈ v ⌉ 𝟘ᵐ[ ok ] ∧ᶜ ⌈ w ⌉ 𝟘ᵐ[ ok ])                                      ≈⟨ ·ᶜ-congˡ $
                                                                             ∧ᶜ-cong (⌈⌉-𝟘ᵐ t) $
                                                                             ∧ᶜ-cong (tailₘ-cong (tailₘ-cong (⌈⌉-𝟘ᵐ B))) $
                                                                             ∧ᶜ-cong (⌈⌉-𝟘ᵐ u) (∧ᶜ-cong (⌈⌉-𝟘ᵐ v) (⌈⌉-𝟘ᵐ w)) ⟩

  ω ·ᶜ (𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ)                                       ≈˘⟨ ·ᶜ-congˡ $
                                                                              ≈ᶜ-trans (≈ᶜ-sym $ ∧ᶜ-idem _) $
                                                                              ∧ᶜ-congˡ $
                                                                              ≈ᶜ-trans (≈ᶜ-sym $ ∧ᶜ-idem _) $
                                                                              ∧ᶜ-congˡ $
                                                                              ≈ᶜ-trans (≈ᶜ-sym $ ∧ᶜ-idem _) $
                                                                              ∧ᶜ-congˡ $
                                                                              ≈ᶜ-sym $ ∧ᶜ-idem _ ⟩

  ω ·ᶜ 𝟘ᶜ                                                                 ≈⟨ ·ᶜ-zeroʳ _ ⟩

  𝟘ᶜ                                                                      ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid
⌈⌉-𝟘ᵐ {ok} (K _ _ t B u v) with Erased-matches-for-K? 𝟘ᵐ[ ok ]
… | yes _ = ⌈⌉-𝟘ᵐ u
… | no _  = begin
  ω ·ᶜ
  (⌈ t ⌉ 𝟘ᵐ[ ok ] ∧ᶜ tailₘ (⌈ B ⌉ 𝟘ᵐ[ ok ]) ∧ᶜ ⌈ u ⌉ 𝟘ᵐ[ ok ] ∧ᶜ
   ⌈ v ⌉ 𝟘ᵐ[ ok ])                                                ≈⟨ ·ᶜ-congˡ $
                                                                     ∧ᶜ-cong (⌈⌉-𝟘ᵐ t) $
                                                                     ∧ᶜ-cong (tailₘ-cong (⌈⌉-𝟘ᵐ B)) $
                                                                     ∧ᶜ-cong (⌈⌉-𝟘ᵐ u) (⌈⌉-𝟘ᵐ v) ⟩

  ω ·ᶜ (𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ)                                     ≈˘⟨ ·ᶜ-congˡ $
                                                                      ≈ᶜ-trans (≈ᶜ-sym $ ∧ᶜ-idem _) $
                                                                      ∧ᶜ-congˡ $
                                                                      ≈ᶜ-trans (≈ᶜ-sym $ ∧ᶜ-idem _) $
                                                                      ∧ᶜ-congˡ $
                                                                      ≈ᶜ-sym $ ∧ᶜ-idem _ ⟩

  ω ·ᶜ 𝟘ᶜ                                                         ≈⟨ ·ᶜ-zeroʳ _ ⟩

  𝟘ᶜ                                                              ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid
⌈⌉-𝟘ᵐ ([]-cong _ _ _ _ _) =
  ≈ᶜ-refl

-- The context ⌈ t ⌉ m does not change (up to _≈ᶜ_) if it is
-- multiplied by ⌜ m ⌝.

·-⌈⌉ :
  ⦃ has-nr : Has-nr semiring-with-meet ⦄ →
  (t : Term n) → ⌜ m ⌝ ·ᶜ ⌈ t ⌉ m ≈ᶜ ⌈ t ⌉ m
·-⌈⌉ {m = 𝟘ᵐ} t = begin
  𝟘 ·ᶜ ⌈ t ⌉ 𝟘ᵐ  ≈⟨ ·ᶜ-zeroˡ _ ⟩
  𝟘ᶜ             ≈˘⟨ ⌈⌉-𝟘ᵐ t ⟩
  ⌈ t ⌉ 𝟘ᵐ       ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid
·-⌈⌉ {m = 𝟙ᵐ} t = begin
  𝟙 ·ᶜ ⌈ t ⌉ 𝟙ᵐ  ≈⟨ ·ᶜ-identityˡ _ ⟩
  ⌈ t ⌉ 𝟙ᵐ       ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid

open import Graded.Modality.Dedicated-nr.Instance

-- For dedicated nr functions the function ⌈_⌉ provides upper bounds
-- for valid modality contexts when the strong unit type is not
-- allowed to be used as a sink: if γ ▸[ m ] t, then γ ≤ᶜ ⌈ t ⌉ m.

usage-upper-bound :
  ⦃ has-nr : Dedicated-nr ⦄ →
  ⦃ no-sink : ¬Starˢ-sink ⦄ →
  γ ▸[ m ] t → γ ≤ᶜ ⌈ t ⌉ m
usage-upper-bound Uₘ     = ≤ᶜ-refl
usage-upper-bound ℕₘ     = ≤ᶜ-refl
usage-upper-bound Emptyₘ = ≤ᶜ-refl
usage-upper-bound Unitₘ  = ≤ᶜ-refl

usage-upper-bound (ΠΣₘ {G = G} ▸F ▸G) =
  +ᶜ-monotone (usage-upper-bound ▸F)
              (subst (_ ≈ᶜ_) (tailₘ-distrib-∧ᶜ (_ ∙ _) (⌈ G ⌉ _))
                     (tailₘ-cong (usage-upper-bound ▸G)))

usage-upper-bound var = ≤ᶜ-refl

usage-upper-bound (lamₘ {t = t} ▸t) =
  subst (_ ≈ᶜ_) (tailₘ-distrib-∧ᶜ (_ ∙ _) (⌈ t ⌉ _))
    (tailₘ-cong (usage-upper-bound ▸t))

usage-upper-bound (▸t ∘ₘ ▸u) =
  +ᶜ-monotone (usage-upper-bound ▸t)
    (·ᶜ-monotoneʳ (usage-upper-bound ▸u))

usage-upper-bound (prodʷₘ t u) =
  +ᶜ-monotone (·ᶜ-monotoneʳ (usage-upper-bound t)) (usage-upper-bound u)
usage-upper-bound (prodˢₘ t u) =
  ∧ᶜ-monotone (·ᶜ-monotoneʳ (usage-upper-bound t))
    (usage-upper-bound u)
usage-upper-bound (fstₘ _ t PE.refl _) = usage-upper-bound t
usage-upper-bound (sndₘ t) = usage-upper-bound t
usage-upper-bound (prodrecₘ t u A _) =
  +ᶜ-monotone (·ᶜ-monotoneʳ (usage-upper-bound t))
              (tailₘ-monotone (tailₘ-monotone (usage-upper-bound u)))

usage-upper-bound zeroₘ    = ≤ᶜ-refl
usage-upper-bound (sucₘ t) = usage-upper-bound t

usage-upper-bound
  ⦃ has-nr = nr₁ ⦄
  (natrecₘ {z = z} {s = s} {n = n} ⦃ has-nr = nr₂ ⦄ γ▸z δ▸s η▸n θ▸A) =
  case Dedicated-nr-propositional nr₁ nr₂ of λ {
    refl →
  case usage-upper-bound γ▸z of λ {
    γ≤γ′ →
  case usage-upper-bound δ▸s of λ {
    δ≤δ′ →
  case usage-upper-bound η▸n of λ {
    η≤η′ →
  nrᶜ-monotone γ≤γ′ (tailₘ-monotone (tailₘ-monotone δ≤δ′)) η≤η′ }}}}

usage-upper-bound (natrec-no-nrₘ _ _ _ _ _ _ _ _) =
  ⊥-elim not-nr-and-no-nr

usage-upper-bound (emptyrecₘ e A) =
  ·ᶜ-monotoneʳ (usage-upper-bound e)

usage-upper-bound starʷₘ = ≤ᶜ-refl
usage-upper-bound ⦃ no-sink = ns ⦄ (starˢₘ prop) =
  ≤ᶜ-reflexive (≈ᶜ-trans (·ᶜ-congˡ (≈ᶜ-sym (prop ns)))
                 (·ᶜ-zeroʳ _))

usage-upper-bound (unitrecₘ t u A ok) =
  +ᶜ-monotone (·ᶜ-monotoneʳ (usage-upper-bound t)) (usage-upper-bound u)

usage-upper-bound {m} (Idₘ {δ} {t} {η} {u} not-ok _ ▸t ▸u)
  with Id-erased?
… | yes ok = ⊥-elim (not-ok ok)
… | no _   = begin
  δ +ᶜ η              ≤⟨ +ᶜ-monotone (usage-upper-bound ▸t) (usage-upper-bound ▸u) ⟩
  ⌈ t ⌉ m +ᶜ ⌈ u ⌉ m  ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

usage-upper-bound (Id₀ₘ ok _ _ _) with Id-erased?
… | no not-ok = ⊥-elim (not-ok ok)
… | yes _     = ≤ᶜ-refl

usage-upper-bound rflₘ =
  ≤ᶜ-refl

usage-upper-bound
  {m}
  (Jₘ {γ₂} {t} {γ₃} {B} {γ₄} {u} {γ₅} {v} {γ₆} {w}
     not-ok _ ▸t ▸B ▸u ▸v ▸w)
  with Erased-matches-for-J? m
… | yes ok = ⊥-elim (not-ok ok)
… | no _   = begin
  ω ·ᶜ (γ₂ ∧ᶜ γ₃ ∧ᶜ γ₄ ∧ᶜ γ₅ ∧ᶜ γ₆)                                      ≤⟨ ·ᶜ-monotoneʳ $
                                                                            ∧ᶜ-monotone (usage-upper-bound ▸t) $
                                                                            ∧ᶜ-monotone (tailₘ-monotone (tailₘ-monotone (usage-upper-bound ▸B))) $
                                                                            ∧ᶜ-monotone (usage-upper-bound ▸u) $
                                                                            ∧ᶜ-monotone (usage-upper-bound ▸v) $
                                                                            usage-upper-bound ▸w ⟩
  ω ·ᶜ
  (⌈ t ⌉ m ∧ᶜ tailₘ (tailₘ (⌈ B ⌉ m)) ∧ᶜ ⌈ u ⌉ m ∧ᶜ ⌈ v ⌉ m ∧ᶜ ⌈ w ⌉ m)  ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

usage-upper-bound {m} (J₀ₘ ok _ _ _ ▸u _ _) with Erased-matches-for-J? m
… | no not-ok = ⊥-elim (not-ok ok)
… | yes _     = usage-upper-bound ▸u

usage-upper-bound
  {m} (Kₘ {γ₂} {t} {γ₃} {B} {γ₄} {u} {γ₅} {v} not-ok _ ▸t ▸B ▸u ▸v)
  with Erased-matches-for-K? m
… | yes ok = ⊥-elim (not-ok ok)
… | no _   = begin
  ω ·ᶜ (γ₂ ∧ᶜ γ₃ ∧ᶜ γ₄ ∧ᶜ γ₅)                              ≤⟨ ·ᶜ-monotoneʳ $
                                                              ∧ᶜ-monotone (usage-upper-bound ▸t) $
                                                              ∧ᶜ-monotone (tailₘ-monotone (usage-upper-bound ▸B)) $
                                                              ∧ᶜ-monotone (usage-upper-bound ▸u) $
                                                              usage-upper-bound ▸v ⟩
  ω ·ᶜ (⌈ t ⌉ m ∧ᶜ tailₘ (⌈ B ⌉ m) ∧ᶜ ⌈ u ⌉ m ∧ᶜ ⌈ v ⌉ m)  ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

usage-upper-bound {m} (K₀ₘ ok _ _ _ ▸u _) with Erased-matches-for-K? m
… | no not-ok = ⊥-elim (not-ok ok)
… | yes _     = usage-upper-bound ▸u

usage-upper-bound ([]-congₘ _ _ _ _) =
  ≤ᶜ-refl

usage-upper-bound (sub t x) = ≤ᶜ-trans x (usage-upper-bound t)


-- A valid modality context can be computed from a well-resourced term
-- (if there is a dedicated nr functions).

usage-inf :
  ⦃ has-nr : Dedicated-nr ⦄ →
  γ ▸[ m ] t → ⌈ t ⌉ m ▸[ m ] t
usage-inf Uₘ = Uₘ
usage-inf ℕₘ = ℕₘ
usage-inf Emptyₘ = Emptyₘ
usage-inf Unitₘ = Unitₘ
usage-inf (ΠΣₘ {G = G} γ▸F δ▸G) =
  ΠΣₘ (usage-inf γ▸F) (Conₘ-interchange₁ (usage-inf δ▸G) δ▸G)
usage-inf var = var
usage-inf (lamₘ {p = p} {t = t} γ▸t) =
  lamₘ (Conₘ-interchange₁ (usage-inf γ▸t) γ▸t)
usage-inf (γ▸t ∘ₘ γ▸t₁) = usage-inf γ▸t ∘ₘ usage-inf γ▸t₁
usage-inf (prodʷₘ γ▸t γ▸t₁) = prodʷₘ (usage-inf γ▸t) (usage-inf γ▸t₁)
usage-inf (prodˢₘ γ▸t γ▸t₁) = prodˢₘ (usage-inf γ▸t) (usage-inf γ▸t₁)
usage-inf (fstₘ m γ▸t PE.refl ok) =
  fstₘ m (usage-inf γ▸t) PE.refl ok
usage-inf (sndₘ γ▸t) = sndₘ (usage-inf γ▸t)
usage-inf {m = m} (prodrecₘ {r = r} {δ = δ} {p = p} {u = u} γ▸t δ▸u η▸A ok) =
  prodrecₘ (usage-inf γ▸t)
           (Conₘ-interchange₂ (usage-inf δ▸u) δ▸u)
           η▸A
           ok
usage-inf zeroₘ = zeroₘ
usage-inf (sucₘ γ▸t) = sucₘ (usage-inf γ▸t)
usage-inf {m = m}
  ⦃ has-nr = nr₁ ⦄
  (natrecₘ {p = p} {r = r} {s = s} ⦃ has-nr = nr₂ ⦄ γ▸z δ▸s η▸n θ▸A) =
  case Dedicated-nr-propositional nr₁ nr₂ of λ {
    refl →
  natrecₘ (usage-inf γ▸z)
          (Conₘ-interchange₂ (usage-inf δ▸s) δ▸s)
          (usage-inf η▸n)
          θ▸A }
usage-inf (natrec-no-nrₘ _ _ _ _ _ _ _ _) =
  ⊥-elim not-nr-and-no-nr
usage-inf (emptyrecₘ γ▸t δ▸A) = emptyrecₘ (usage-inf γ▸t) δ▸A
usage-inf starʷₘ = starʷₘ
usage-inf (starˢₘ prop) = starₘ
usage-inf (unitrecₘ γ▸t δ▸u η▸A ok) =
  unitrecₘ (usage-inf γ▸t) (usage-inf δ▸u) η▸A ok
usage-inf (Idₘ not-ok ▸A ▸t ▸u) with Id-erased?
… | yes ok = ⊥-elim (not-ok ok)
… | no _   = Idₘ not-ok ▸A (usage-inf ▸t) (usage-inf ▸u)
usage-inf (Id₀ₘ ok ▸A ▸t ▸u) with Id-erased?
… | no not-ok = ⊥-elim (not-ok ok)
… | yes _     = Id₀ₘ ok ▸A ▸t ▸u
usage-inf rflₘ =
  rflₘ
usage-inf {m} (Jₘ {p} {q} {B} not-ok ▸A ▸t ▸B ▸u ▸v ▸w)
  with Erased-matches-for-J? m
… | yes ok = ⊥-elim (not-ok ok)
… | no _   =
  Jₘ not-ok ▸A (usage-inf ▸t)
     (Conₘ-interchange₂ (usage-inf ▸B) ▸B)
     (usage-inf ▸u) (usage-inf ▸v) (usage-inf ▸w)
usage-inf {m} (J₀ₘ ok ▸A ▸t ▸B ▸u ▸v ▸w) with Erased-matches-for-J? m
… | no not-ok = ⊥-elim (not-ok ok)
… | yes _     = J₀ₘ ok ▸A ▸t ▸B (usage-inf ▸u) ▸v ▸w
usage-inf {m} (Kₘ {p} {B} not-ok ▸A ▸t ▸B ▸u ▸v)
  with Erased-matches-for-K? m
… | yes ok = ⊥-elim (not-ok ok)
… | no _   =
  Kₘ not-ok ▸A (usage-inf ▸t)
     (Conₘ-interchange₁ (usage-inf ▸B) ▸B)
     (usage-inf ▸u) (usage-inf ▸v)
usage-inf {m} (K₀ₘ ok ▸A ▸t ▸B ▸u ▸v) with Erased-matches-for-K? m
… | no not-ok = ⊥-elim (not-ok ok)
… | yes _     = K₀ₘ ok ▸A ▸t ▸B (usage-inf ▸u) ▸v
usage-inf ([]-congₘ ▸A ▸t ▸u ▸v) =
  []-congₘ ▸A ▸t ▸u ▸v
usage-inf (sub γ▸t x) = usage-inf γ▸t

------------------------------------------------------------------------
-- A negative result

module _ (TR : Type-restrictions) where

  open Definition.Typed TR

  -- It is always the case that Γ ⊢ t ∷ A implies Γ ⊢ A (see
  -- Definition.Typed.Consequences.Syntactic.syntacticTerm), but if
  -- Γ ⊢ t ∷ A and γ ▸[ 𝟙ᵐ ] t always imply γ ▸[ 𝟙ᵐ ] A, then the
  -- modality is trivial.

  ▸-term→▸-type :
    (∀ {n} {Γ : Con Term n} {t A : Term n} {γ : Conₘ n} →
       Γ ⊢ t ∷ A → γ ▸[ 𝟙ᵐ ] t → γ ▸[ 𝟙ᵐ ] A) →
    Trivial
  ▸-term→▸-type hyp =
    case inv-usage-var (hyp ⊢t ▸t) of λ {
      (ε ∙ 𝟘≤𝟙 ∙ 𝟙≤𝟘) →
    ≤-antisym 𝟙≤𝟘 𝟘≤𝟙 }
    where
    Γ′ = ε ∙ U ∙ var x0
    t′ = var x0
    A′ = var x1
    γ′ = ε ∙ 𝟘 ∙ 𝟙

    ⊢U : ⊢ ε ∙ U
    ⊢U = ε ∙ Uⱼ ε

    ⊢Γ : ⊢ Γ′
    ⊢Γ = ⊢U ∙ univ (var ⊢U here)

    ⊢t : Γ′ ⊢ t′ ∷ A′
    ⊢t = var ⊢Γ here

    ▸t : γ′ ▸[ 𝟙ᵐ ] t′
    ▸t = var
