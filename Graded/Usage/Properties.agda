------------------------------------------------------------------------
-- Properties of the usage relation.
------------------------------------------------------------------------

import Graded.Modality
open import Graded.Usage.Restrictions

module Graded.Usage.Properties
  {a} {M : Set a}
  (open Graded.Modality M)
  (𝕄 : Modality)
  (R : Usage-restrictions M)
  where

open Modality 𝕄
open Usage-restrictions R

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Usage 𝕄 R
open import Graded.Usage.Inversion 𝕄 R
open import Graded.Modality.Dedicated-star 𝕄
open import Graded.Modality.Natrec-star-instances
open import Graded.Modality.Properties 𝕄
open import Graded.Mode 𝕄

import Definition.Typed
open import Definition.Typed.Restrictions M
open import Definition.Untyped M hiding (_∷_)

open import Tools.Bool using (Bool; T)
open import Tools.Fin
open import Tools.Function
open import Tools.Level
open import Tools.Nat using (Nat; 1+)
open import Tools.Nullary
open import Tools.Product
open import Tools.PropositionalEquality as PE
open import Tools.Sum
open import Tools.Unit
import Tools.Reasoning.Equivalence
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality

private
  variable
    n : Nat
    Γ : Con Term n
    A F t u v : Term n
    G : Term (1+ n)
    γ δ η θ χ : Conₘ n
    p q r : M
    m m₁ m₂ m′ : Mode
    b : Bool
    ok : T b
    x : Fin n

-- Variables only have one annotation in a context

unique-var-usage : x ◂ p ∈ γ → x ◂ q ∈ γ → p PE.≡ q
unique-var-usage here here = PE.refl
unique-var-usage (there x) (there y) = unique-var-usage x y

-- Variable lookup and the usage relation for variables match

var-usage-lookup : x ◂ p ∈ γ → γ ⟨ x ⟩ ≡ p
var-usage-lookup here = PE.refl
var-usage-lookup (there x) = var-usage-lookup x

------------------------------------------------------------------------
-- Replacing one usage mode with another

-- γ ▸[_] t respects _≡_.

▸-cong : m₁ ≡ m₂ → γ ▸[ m₁ ] t → γ ▸[ m₂ ] t
▸-cong = subst (_ ▸[_] _)

-- If 𝟘ᵐ is not allowed, then one can convert usage modes freely.

▸-without-𝟘ᵐ : ¬ T 𝟘ᵐ-allowed → γ ▸[ m ] t → γ ▸[ m′ ] t
▸-without-𝟘ᵐ not-ok =
  ▸-cong (Mode-propositional-without-𝟘ᵐ not-ok)

-- If 𝟙 ≡ 𝟘, then one can convert usage modes freely.

▸-𝟙≡𝟘 : 𝟙 ≡ 𝟘 → γ ▸[ m ] t → γ ▸[ m′ ] t
▸-𝟙≡𝟘 𝟙≡𝟘 = ▸-without-𝟘ᵐ (flip 𝟘ᵐ→𝟙≢𝟘 𝟙≡𝟘)

------------------------------------------------------------------------
-- The lemma ▸-· and some corollaries

-- The relation _▸[_]_ respects multiplication (in a certain sense).

▸-· : γ ▸[ m ] t → ⌜ m′ ⌝ ·ᶜ γ ▸[ m′ ·ᵐ m ] t
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
▸-· {m′ = m′} (prodᵣₘ {γ = γ} {p = p} {δ = δ} t u) = sub
  (prodᵣₘ (▸-cong (PE.sym (·ᵐ-ᵐ·-assoc m′)) (▸-· t)) (▸-· u))
  (begin
     ⌜ m′ ⌝ ·ᶜ (p ·ᶜ γ +ᶜ δ)           ≈⟨ ·ᶜ-distribˡ-+ᶜ _ _ _ ⟩
     ⌜ m′ ⌝ ·ᶜ p ·ᶜ γ +ᶜ ⌜ m′ ⌝ ·ᶜ δ   ≈˘⟨ +ᶜ-congʳ (·ᶜ-assoc _ _ _) ⟩
     (⌜ m′ ⌝ · p) ·ᶜ γ +ᶜ ⌜ m′ ⌝ ·ᶜ δ  ≈⟨ +ᶜ-congʳ (·ᶜ-congʳ (⌜⌝-·-comm m′)) ⟩
     (p · ⌜ m′ ⌝) ·ᶜ γ +ᶜ ⌜ m′ ⌝ ·ᶜ δ  ≈⟨ +ᶜ-congʳ (·ᶜ-assoc _ _ _) ⟩
     p ·ᶜ ⌜ m′ ⌝ ·ᶜ γ +ᶜ ⌜ m′ ⌝ ·ᶜ δ   ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
▸-· {m′ = m′} (prodₚₘ {γ = γ} {m = m} {p = p} {δ = δ} t u) = sub
  (prodₚₘ (▸-cong (PE.sym (·ᵐ-ᵐ·-assoc m′)) (▸-· t)) (▸-· u))
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
     ok)
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
     ⌜ m′ ⌝ ·ᶜ (γ ∧ᶜ η) ⊛ᶜ δ +ᶜ p ·ᶜ η ▷ r                                ≈⟨ ⌜⌝-·ᶜ-distribˡ-⊛ᶜ m′ ⟩
     (⌜ m′ ⌝ ·ᶜ (γ ∧ᶜ η)) ⊛ᶜ ⌜ m′ ⌝ ·ᶜ (δ +ᶜ p ·ᶜ η) ▷ r                  ≈⟨ ⊛ᶜ-cong (·ᶜ-distribˡ-∧ᶜ _ _ _) (·ᶜ-distribˡ-+ᶜ _ _ _) refl ⟩
     (⌜ m′ ⌝ ·ᶜ γ ∧ᶜ ⌜ m′ ⌝ ·ᶜ η) ⊛ᶜ ⌜ m′ ⌝ ·ᶜ δ +ᶜ ⌜ m′ ⌝ ·ᶜ p ·ᶜ η ▷ r  ≈⟨ ⊛ᵣᶜ-congˡ
                                                                               (+ᶜ-congˡ
                                                                                  (≈ᶜ-trans (≈ᶜ-sym (·ᶜ-assoc _ _ _))
                                                                                     (≈ᶜ-trans (·ᶜ-congʳ (⌜⌝-·-comm m′))
                                                                                        (·ᶜ-assoc _ _ _)))) ⟩
     (⌜ m′ ⌝ ·ᶜ γ ∧ᶜ ⌜ m′ ⌝ ·ᶜ η) ⊛ᶜ ⌜ m′ ⌝ ·ᶜ δ +ᶜ p ·ᶜ ⌜ m′ ⌝ ·ᶜ η ▷ r  ∎)
  where
  open import Graded.Modality.Dedicated-star.Instance
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
▸-· {m = m} {m′ = m′}
  (natrec-no-starₘ {γ = γ} {δ = δ} {p = p} {r = r} {η = η} {χ = χ}
     γ▸z δ▸s η▸n θ▸A fix) =
  natrec-no-starₘ (▸-· γ▸z)
    (sub (▸-· δ▸s)
       (≤ᶜ-reflexive (≈ᶜ-refl ∙ ·ᵐ-·-assoc m′ ∙ ·ᵐ-·-assoc m′)))
    (▸-· η▸n)
    θ▸A
    (begin
       ⌜ m′ ⌝ ·ᶜ χ                                              ≤⟨ ·ᶜ-monotoneʳ fix ⟩

       ⌜ m′ ⌝ ·ᶜ (γ ∧ᶜ η ∧ᶜ (δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ χ))            ≈⟨ ≈ᶜ-trans (·ᶜ-distribˡ-∧ᶜ _ _ _) $
                                                                   ∧ᶜ-congˡ $
                                                                   ≈ᶜ-trans (·ᶜ-distribˡ-∧ᶜ _ _ _) $
                                                                   ∧ᶜ-congˡ $
                                                                   ≈ᶜ-trans (·ᶜ-distribˡ-+ᶜ _ _ _) $
                                                                   +ᶜ-congˡ $
                                                                   ·ᶜ-distribˡ-+ᶜ _ _ _ ⟩
       ⌜ m′ ⌝ ·ᶜ γ ∧ᶜ ⌜ m′ ⌝ ·ᶜ η ∧ᶜ
       (⌜ m′ ⌝ ·ᶜ δ +ᶜ ⌜ m′ ⌝ ·ᶜ p ·ᶜ η +ᶜ ⌜ m′ ⌝ ·ᶜ r ·ᶜ χ)    ≈⟨ ∧ᶜ-congˡ $ ∧ᶜ-congˡ $ +ᶜ-congˡ $ +ᶜ-cong
                                                                   (≈ᶜ-trans (≈ᶜ-sym (·ᶜ-assoc _ _ _)) $
                                                                    ≈ᶜ-trans (·ᶜ-congʳ (⌜⌝-·-comm m′)) $
                                                                    ·ᶜ-assoc _ _ _)
                                                                   (≈ᶜ-trans (≈ᶜ-sym (·ᶜ-assoc _ _ _)) $
                                                                    ≈ᶜ-trans (·ᶜ-congʳ (⌜⌝-·-comm m′)) $
                                                                    ·ᶜ-assoc _ _ _) ⟩
       ⌜ m′ ⌝ ·ᶜ γ ∧ᶜ ⌜ m′ ⌝ ·ᶜ η ∧ᶜ
       (⌜ m′ ⌝ ·ᶜ δ +ᶜ p ·ᶜ ⌜ m′ ⌝ ·ᶜ η +ᶜ r ·ᶜ ⌜ m′ ⌝ ·ᶜ χ)    ∎)
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
▸-· starₘ =
  sub starₘ (≤ᶜ-reflexive (·ᶜ-zeroʳ _))
▸-· (sub γ▸t δ≤γ) =
  sub (▸-· γ▸t) (·ᶜ-monotoneʳ δ≤γ)

-- The relation _▸[_]_ respects multiplication (in a certain sense).

▸-·′ : γ ▸[ m ] t → ⌜ m ⌝ ·ᶜ γ ▸[ m ] t
▸-·′ ▸t = ▸-cong ·ᵐ-idem (▸-· ▸t)

-- If a term is well-resourced with respect to any context and mode,
-- then it is well-resourced with respect to the zero usage context
-- and the mode 𝟘ᵐ[ ok ].

▸-𝟘 : γ ▸[ m ] t → 𝟘ᶜ ▸[ 𝟘ᵐ[ ok ] ] t
▸-𝟘 {γ = γ} ▸t = sub
  (▸-· ▸t)
  (begin
     𝟘ᶜ      ≈˘⟨ ·ᶜ-zeroˡ _ ⟩
     𝟘 ·ᶜ γ  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

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
    ⊥-elim (⌞⌟≡𝟙ᵐ→≢𝟘 ok ⌞q⌟≡𝟙ᵐ (𝟘≮ ok (begin
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

-- Usage-restrictions-satisfied t means that all the usage
-- restrictions hold for every subterm in t.

Usage-restrictions-satisfied : Term n → Set a
Usage-restrictions-satisfied = λ where
  (prodrec r p q A t u)   → Prodrec-allowed r p q ×
                            Usage-restrictions-satisfied A ×
                            Usage-restrictions-satisfied t ×
                            Usage-restrictions-satisfied u
  (ΠΣ⟨ _ ⟩ _ , _ ▷ A ▹ B) → Usage-restrictions-satisfied A ×
                            Usage-restrictions-satisfied B
  (lam _ t)               → Usage-restrictions-satisfied t
  (t ∘⟨ _ ⟩ u)            → Usage-restrictions-satisfied t ×
                            Usage-restrictions-satisfied u
  (prod _ _ t u)          → Usage-restrictions-satisfied t ×
                            Usage-restrictions-satisfied u
  (fst _ t)               → Usage-restrictions-satisfied t
  (snd _ t)               → Usage-restrictions-satisfied t
  (suc t)                 → Usage-restrictions-satisfied t
  (natrec _ _ _ A t u v)  → Usage-restrictions-satisfied A ×
                            Usage-restrictions-satisfied t ×
                            Usage-restrictions-satisfied u ×
                            Usage-restrictions-satisfied v
  (emptyrec _ A t)        → Usage-restrictions-satisfied A ×
                            Usage-restrictions-satisfied t
  (var _)                 → Lift _ ⊤
  U                       → Lift _ ⊤
  ℕ                       → Lift _ ⊤
  Empty                   → Lift _ ⊤
  Unit                    → Lift _ ⊤
  zero                    → Lift _ ⊤
  star                    → Lift _ ⊤

-- If t is well-resourced (with respect to any context and mode), then
-- Usage-restrictions-satisfied t holds.

▸→Usage-restrictions-satisfied :
  γ ▸[ m ] t → Usage-restrictions-satisfied t
▸→Usage-restrictions-satisfied = λ where
  Uₘ →
    _
  ℕₘ →
    _
  Emptyₘ →
    _
  Unitₘ →
    _
  (ΠΣₘ ▸A ▸B) →
    ▸→Usage-restrictions-satisfied ▸A ,
    ▸→Usage-restrictions-satisfied ▸B
  var →
    _
  (lamₘ ▸t) →
    ▸→Usage-restrictions-satisfied ▸t
  (▸t ∘ₘ ▸u) →
    ▸→Usage-restrictions-satisfied ▸t ,
    ▸→Usage-restrictions-satisfied ▸u
  (prodᵣₘ ▸t ▸u) →
    ▸→Usage-restrictions-satisfied ▸t ,
    ▸→Usage-restrictions-satisfied ▸u
  (prodₚₘ ▸t ▸u) →
    ▸→Usage-restrictions-satisfied ▸t ,
    ▸→Usage-restrictions-satisfied ▸u
  (fstₘ _ ▸t _ _) →
    ▸→Usage-restrictions-satisfied ▸t
  (sndₘ ▸t) →
    ▸→Usage-restrictions-satisfied ▸t
  (prodrecₘ ▸t ▸u ▸A ok) →
    ok ,
    ▸→Usage-restrictions-satisfied ▸A ,
    ▸→Usage-restrictions-satisfied ▸t ,
    ▸→Usage-restrictions-satisfied ▸u
  zeroₘ →
    _
  (sucₘ ▸t) →
    ▸→Usage-restrictions-satisfied ▸t
  (natrecₘ ▸t ▸u ▸v ▸A) →
    ▸→Usage-restrictions-satisfied ▸A ,
    ▸→Usage-restrictions-satisfied ▸t ,
    ▸→Usage-restrictions-satisfied ▸u ,
    ▸→Usage-restrictions-satisfied ▸v
  (natrec-no-starₘ ▸t ▸u ▸v ▸A _) →
    ▸→Usage-restrictions-satisfied ▸A ,
    ▸→Usage-restrictions-satisfied ▸t ,
    ▸→Usage-restrictions-satisfied ▸u ,
    ▸→Usage-restrictions-satisfied ▸v
  (emptyrecₘ ▸t ▸A) →
    ▸→Usage-restrictions-satisfied ▸A ,
    ▸→Usage-restrictions-satisfied ▸t
  starₘ →
    _
  (sub ▸t _) →
    ▸→Usage-restrictions-satisfied ▸t

-- If Usage-restrictions-satisfied t holds, then t is well-resourced
-- with respect to 𝟘ᶜ and 𝟘ᵐ[ ok ].

Usage-restrictions-satisfied→▸[𝟘ᵐ] :
  Usage-restrictions-satisfied t → 𝟘ᶜ ▸[ 𝟘ᵐ[ ok ] ] t
Usage-restrictions-satisfied→▸[𝟘ᵐ] {ok = 𝟘ᵐ-ok} = lemma _
  where
  open import Graded.Modality.Dedicated-star.Instance

  lemma :
    (t : Term n) → Usage-restrictions-satisfied t →
    𝟘ᶜ ▸[ 𝟘ᵐ[ 𝟘ᵐ-ok ] ] t
  lemma = λ where
    (prodrec r p q A t u) (ok , A-ok , t-ok , u-ok) →
      sub (prodrecₘ (lemma t t-ok)
             (sub (lemma u u-ok) $
              let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
                𝟘ᶜ ∙ 𝟘 · r · p ∙ 𝟘 · r  ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ∙ ·-zeroˡ _ ⟩
                𝟘ᶜ                      ∎)
             (sub (▸-cong (PE.sym (𝟘ᵐ?≡𝟘ᵐ {ok = 𝟘ᵐ-ok})) $
                   lemma A A-ok) $
              let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
                𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · q  ≈⟨ ≈ᶜ-refl ∙ ·-congʳ (cong ⌜_⌝ (𝟘ᵐ?≡𝟘ᵐ {ok = 𝟘ᵐ-ok})) ⟩
                𝟘ᶜ ∙ 𝟘 · q        ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
                𝟘ᶜ                ∎)
             ok) $
      let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
        𝟘ᶜ             ≈˘⟨ ·ᶜ-zeroʳ _ ⟩
        r ·ᶜ 𝟘ᶜ        ≈˘⟨ +ᶜ-identityʳ _ ⟩
        r ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ  ∎
    (ΠΣ⟨ _ ⟩ _ , q ▷ A ▹ B) (A-ok , B-ok) →
      sub (ΠΣₘ (lemma A A-ok) $ sub (lemma B B-ok) $
           let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
             𝟘ᶜ ∙ 𝟘 · q  ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
             𝟘ᶜ          ∎) $
      let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
        𝟘ᶜ        ≈˘⟨ +ᶜ-identityˡ _ ⟩
        𝟘ᶜ +ᶜ 𝟘ᶜ  ∎
    (lam p t) t-ok →
      let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
      lamₘ $ sub (lemma t t-ok) $ begin
        𝟘ᶜ ∙ 𝟘 · p  ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
        𝟘ᶜ          ∎
    (t ∘⟨ p ⟩ u) (t-ok , u-ok) →
      let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
      sub (lemma t t-ok ∘ₘ lemma u u-ok) $
      begin
        𝟘ᶜ             ≈˘⟨ ·ᶜ-zeroʳ _ ⟩
        p ·ᶜ 𝟘ᶜ        ≈˘⟨ +ᶜ-identityˡ _ ⟩
        𝟘ᶜ +ᶜ p ·ᶜ 𝟘ᶜ  ∎
    (prodₚ p t u) (t-ok , u-ok) →
      let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
      sub (prodₚₘ (lemma t t-ok) (lemma u u-ok)) $
      begin
        𝟘ᶜ             ≈˘⟨ ∧ᶜ-idem _ ⟩
        𝟘ᶜ ∧ᶜ 𝟘ᶜ       ≈˘⟨ ∧ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
        p ·ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ  ∎
    (prodᵣ p t u) (t-ok , u-ok) →
      let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
      sub (prodᵣₘ (lemma t t-ok) (lemma u u-ok)) $
      begin
        𝟘ᶜ             ≈˘⟨ +ᶜ-identityˡ _ ⟩
        𝟘ᶜ +ᶜ 𝟘ᶜ       ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
        p ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ  ∎
    (fst p t) t-ok →
      fstₘ 𝟘ᵐ[ 𝟘ᵐ-ok ] (lemma t t-ok) refl (λ ())
    (snd _ t) t-ok →
      sndₘ (lemma t t-ok)
    (suc t) t-ok →
      sucₘ (lemma t t-ok)
    (natrec p q r A t u v) (A-ok , t-ok , u-ok , v-ok) →
      let t-lemma =
            lemma t t-ok
          u-lemma =
            sub (lemma u u-ok) $
            let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
              𝟘ᶜ ∙ 𝟘 · p ∙ 𝟘 · r  ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ∙ ·-zeroˡ _ ⟩
              𝟘ᶜ                  ∎
          v-lemma =
            lemma v v-ok
          A-lemma =
            sub (▸-cong (PE.sym (𝟘ᵐ?≡𝟘ᵐ {ok = 𝟘ᵐ-ok})) $
                 lemma A A-ok) $
            let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
              𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · q  ≈⟨ ≈ᶜ-refl ∙ ·-congʳ (cong ⌜_⌝ (𝟘ᵐ?≡𝟘ᵐ {ok = 𝟘ᵐ-ok})) ⟩
              𝟘ᶜ ∙ 𝟘 · q        ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
              𝟘ᶜ                ∎
      in case dedicated-star? of λ where
        does-have-star →
          sub (natrecₘ t-lemma u-lemma v-lemma A-lemma) $
          let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
            𝟘ᶜ                               ≈˘⟨ ⊛ᶜ-idem-𝟘ᶜ _ ⟩
            𝟘ᶜ ⊛ᶜ 𝟘ᶜ ▷ r                     ≈˘⟨ ⊛ᵣᶜ-congˡ (·ᶜ-zeroʳ _) ⟩
            𝟘ᶜ ⊛ᶜ p ·ᶜ 𝟘ᶜ ▷ r                ≈˘⟨ ⊛ᵣᶜ-cong (∧ᶜ-idem _) (+ᶜ-identityˡ _) ⟩
            (𝟘ᶜ ∧ᶜ 𝟘ᶜ) ⊛ᶜ 𝟘ᶜ +ᶜ p ·ᶜ 𝟘ᶜ ▷ r  ∎
        does-not-have-star →
          natrec-no-starₘ t-lemma u-lemma v-lemma A-lemma $
          let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
            𝟘ᶜ                                        ≈˘⟨ ∧ᶜ-idem _ ⟩
            𝟘ᶜ ∧ᶜ 𝟘ᶜ                                  ≈˘⟨ ∧ᶜ-congˡ (+ᶜ-identityˡ _) ⟩
            𝟘ᶜ ∧ᶜ (𝟘ᶜ +ᶜ 𝟘ᶜ)                          ≈˘⟨ ∧ᶜ-congˡ (+ᶜ-cong (·ᶜ-zeroʳ _) (·ᶜ-zeroʳ _)) ⟩
            𝟘ᶜ ∧ᶜ (p ·ᶜ 𝟘ᶜ +ᶜ r ·ᶜ 𝟘ᶜ)                ≈˘⟨ ∧ᶜ-cong (∧ᶜ-idem _) (+ᶜ-identityˡ _) ⟩
            (𝟘ᶜ ∧ᶜ 𝟘ᶜ) ∧ᶜ (𝟘ᶜ +ᶜ p ·ᶜ 𝟘ᶜ +ᶜ r ·ᶜ 𝟘ᶜ)  ≈⟨ ∧ᶜ-assoc _ _ _ ⟩
            𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ (𝟘ᶜ +ᶜ p ·ᶜ 𝟘ᶜ +ᶜ r ·ᶜ 𝟘ᶜ)    ∎
    (emptyrec p A t) (A-ok , t-ok) →
      let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
      sub (emptyrecₘ (lemma t t-ok) $
           ▸-cong (PE.sym (𝟘ᵐ?≡𝟘ᵐ {ok = 𝟘ᵐ-ok})) $
           lemma A A-ok) $
      begin
        𝟘ᶜ       ≈˘⟨ ·ᶜ-zeroʳ _ ⟩
        p ·ᶜ 𝟘ᶜ  ∎
    (var x) _ →
      let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
      sub var $ begin
        𝟘ᶜ          ≡˘⟨ 𝟘ᶜ,≔𝟘 ⟩
        𝟘ᶜ , x ≔ 𝟘  ∎
    U _ →
      Uₘ
    ℕ _ →
      ℕₘ
    Empty _ →
      Emptyₘ
    Unit _ →
      Unitₘ
    zero _ →
      zeroₘ
    star _ →
      starₘ

-- An alternative characterisation of 𝟘ᶜ ▸[ 𝟘ᵐ[ ok ] ] t.

𝟘ᶜ▸[𝟘ᵐ]⇔ : 𝟘ᶜ ▸[ 𝟘ᵐ[ ok ] ] t ⇔ Usage-restrictions-satisfied t
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
▸-𝟘ᵐ (prodᵣₘ {γ = γ} {p = p} {δ = δ} γ▸ δ▸) = begin
  p ·ᶜ γ +ᶜ δ    ≤⟨ +ᶜ-monotone (·ᶜ-monotoneʳ (▸-𝟘ᵐ γ▸)) (▸-𝟘ᵐ δ▸) ⟩
  p ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ  ≈⟨ +ᶜ-identityʳ _ ⟩
  p ·ᶜ 𝟘ᶜ        ≈⟨ ·ᶜ-zeroʳ _ ⟩
  𝟘ᶜ             ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
▸-𝟘ᵐ (prodₚₘ {γ = γ} {p = p} {δ = δ} γ▸ δ▸) = begin
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
  (γ ∧ᶜ η) ⊛ᶜ δ +ᶜ p ·ᶜ η ▷ r      ≤⟨ ⊛ᶜ-monotone (∧ᶜ-monotone (▸-𝟘ᵐ γ▸) (▸-𝟘ᵐ η▸)) $
                                      +ᶜ-monotone (tailₘ-monotone (tailₘ-monotone (▸-𝟘ᵐ δ▸))) $
                                      ·ᶜ-monotoneʳ (▸-𝟘ᵐ η▸) ⟩
  (𝟘ᶜ ∧ᶜ 𝟘ᶜ) ⊛ᶜ 𝟘ᶜ +ᶜ p ·ᶜ 𝟘ᶜ ▷ r  ≈⟨ ⊛ᵣᶜ-cong (∧ᶜ-idem _) (+ᶜ-identityˡ _) ⟩
  𝟘ᶜ ⊛ᶜ p ·ᶜ 𝟘ᶜ ▷ r                ≈⟨ ⊛ᵣᶜ-congˡ (·ᶜ-zeroʳ _) ⟩
  𝟘ᶜ ⊛ᶜ 𝟘ᶜ ▷ r                     ≈⟨ ⊛ᶜ-idem-𝟘ᶜ _ ⟩
  𝟘ᶜ                               ∎
  where
  open import Graded.Modality.Dedicated-star.Instance
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
▸-𝟘ᵐ
  (natrec-no-starₘ {γ = γ} {δ = δ} {p = p} {r = r} {η = η} {χ = χ}
     γ▸ _ _ _ fix) = begin
  χ                                  ≤⟨ fix ⟩
  γ ∧ᶜ η ∧ᶜ (δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ χ)  ≤⟨ ∧ᶜ-decreasingˡ _ _ ⟩
  γ                                  ≤⟨ ▸-𝟘ᵐ γ▸ ⟩
  𝟘ᶜ                                 ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
▸-𝟘ᵐ (emptyrecₘ {γ = γ} {p = p} γ▸ _) = begin
  p ·ᶜ γ   ≤⟨ ·ᶜ-monotoneʳ (▸-𝟘ᵐ γ▸) ⟩
  p ·ᶜ 𝟘ᶜ  ≈⟨ ·ᶜ-zeroʳ _ ⟩
  𝟘ᶜ       ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
▸-𝟘ᵐ starₘ =
  ≤ᶜ-refl
▸-𝟘ᵐ (sub {γ = γ} {δ = δ} γ▸ δ≤γ) = begin
  δ   ≤⟨ δ≤γ ⟩
  γ   ≤⟨ ▸-𝟘ᵐ γ▸ ⟩
  𝟘ᶜ  ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- An alternative characterisation of γ ▸[ 𝟘ᵐ[ ok ] ] t.

▸[𝟘ᵐ]⇔ : γ ▸[ 𝟘ᵐ[ ok ] ] t ⇔ (γ ≤ᶜ 𝟘ᶜ × Usage-restrictions-satisfied t)
▸[𝟘ᵐ]⇔ =
    (λ ▸t → ▸-𝟘ᵐ ▸t , ▸→Usage-restrictions-satisfied ▸t)
  , (λ (γ≤𝟘 , ok) → sub (Usage-restrictions-satisfied→▸[𝟘ᵐ] ok) γ≤𝟘)

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
  ≡𝟘→⌞⌟≡𝟘ᵐ (+-positiveˡ ok (⌞⌟≡𝟘ᵐ→≡𝟘 ⌞p+q⌟≡𝟘ᵐ))

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
  ≡𝟘→⌞⌟≡𝟘ᵐ (∧-positiveˡ ok (⌞⌟≡𝟘ᵐ→≡𝟘 ⌞p∧q⌟≡𝟘ᵐ))

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
  ≡𝟘→⌞⌟≡𝟘ᵐ (⊛≡𝟘ˡ ok (⌞⌟≡𝟘ᵐ→≡𝟘 ⌞p⊛q▷r⌟≡𝟘ᵐ))

-- A kind of inversion lemma for _▸[_]_ related to the star operation.

▸-⌞⊛⌟ʳ :
  ⦃ has-star : Has-star semiring-with-meet ⦄ →
  ⌜ ⌞ p ⊛ q ▷ r ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p ⊛ q ▷ r ⌟ ] t →
  ⌜ ⌞ q ⌟ ⌝ ·ᶜ γ ▸[ ⌞ q ⌟ ] t
▸-⌞⊛⌟ʳ = ▸-conv λ ok ⌞p⊛q▷r⌟≡𝟘ᵐ →
  ≡𝟘→⌞⌟≡𝟘ᵐ (⊛≡𝟘ʳ ok (⌞⌟≡𝟘ᵐ→≡𝟘 ⌞p⊛q▷r⌟≡𝟘ᵐ))

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
  (prodᵣₘ {γ = γ} {p = p} {δ = δ} ▸t ▸u)
  (prodᵣₘ {γ = γ′} {δ = δ′} ▸t′ ▸u′) x = subst
  (_▸[ _ ] _)
  (p ·ᶜ (γ , x ≔ γ′ ⟨ x ⟩) +ᶜ (δ , x ≔ δ′ ⟨ x ⟩)      ≡˘⟨ cong (_+ᶜ _) (update-distrib-·ᶜ _ _ _ _) ⟩
   (p ·ᶜ γ , x ≔ p · γ′ ⟨ x ⟩) +ᶜ (δ , x ≔ δ′ ⟨ x ⟩)  ≡˘⟨ update-distrib-+ᶜ _ _ _ _ _ ⟩
   p ·ᶜ γ +ᶜ δ , x ≔ p · γ′ ⟨ x ⟩ + δ′ ⟨ x ⟩          ≡˘⟨ cong (λ γ → _ , x ≔ γ + _) (lookup-distrib-·ᶜ γ′ _ _) ⟩
   p ·ᶜ γ +ᶜ δ , x ≔ (p ·ᶜ γ′) ⟨ x ⟩ + δ′ ⟨ x ⟩       ≡˘⟨ cong (_ , _ ≔_) (lookup-distrib-+ᶜ (_ ·ᶜ γ′) _ _) ⟩
   p ·ᶜ γ +ᶜ δ , x ≔ (p ·ᶜ γ′ +ᶜ δ′) ⟨ x ⟩            ∎)
  (prodᵣₘ (Conₘ-interchange ▸t ▸t′ x) (Conₘ-interchange ▸u ▸u′ x))
  where
  open Tools.Reasoning.PropositionalEquality

Conₘ-interchange
  (prodₚₘ {γ = γ} {p = p} {δ = δ} ▸t ▸u)
  (prodₚₘ {γ = γ′} {δ = δ′} ▸t′ ▸u′) x = subst
  (_▸[ _ ] _)
  (p ·ᶜ (γ , x ≔ γ′ ⟨ x ⟩) ∧ᶜ (δ , x ≔ δ′ ⟨ x ⟩)      ≡˘⟨ cong (_∧ᶜ _) (update-distrib-·ᶜ _ _ _ _) ⟩
   (p ·ᶜ γ , x ≔ p · γ′ ⟨ x ⟩) ∧ᶜ (δ , x ≔ δ′ ⟨ x ⟩)  ≡˘⟨ update-distrib-∧ᶜ _ _ _ _ _ ⟩
   p ·ᶜ γ ∧ᶜ δ , x ≔ p · γ′ ⟨ x ⟩ ∧ δ′ ⟨ x ⟩          ≡˘⟨ cong (λ p → _ , x ≔ p ∧ _) (lookup-distrib-·ᶜ γ′ _ _) ⟩
   p ·ᶜ γ ∧ᶜ δ , x ≔ (p ·ᶜ γ′) ⟨ x ⟩ ∧ δ′ ⟨ x ⟩       ≡˘⟨ cong (_ , _ ≔_) (lookup-distrib-∧ᶜ (_ ·ᶜ γ′) _ _) ⟩
   p ·ᶜ γ ∧ᶜ δ , x ≔ (p ·ᶜ γ′ ∧ᶜ δ′) ⟨ x ⟩            ∎)
  (prodₚₘ (Conₘ-interchange ▸t ▸t′ x) (Conₘ-interchange ▸u ▸u′ x))
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
       (Conₘ-interchange δ▸t δ▸t₁ (x +1 +1))
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
     ⦃ has-star = s₁ ⦄ γ▸z δ▸s η▸n θ▸A)
  (natrecₘ {γ = γ′} {δ = δ′} {η = η′}
     ⦃ has-star = s₂ ⦄ γ′▸z δ′▸s η′▸n _)
  x =
  case Dedicated-star-propositional s₁ s₂ of λ {
    refl →
  flip (subst (_▸[ _ ] _))
    (natrecₘ
       (Conₘ-interchange γ▸z γ′▸z x)
       (Conₘ-interchange δ▸s δ′▸s (x +1 +1))
       (Conₘ-interchange η▸n η′▸n x)
       θ▸A)
    ((γ' ∧ᶜ η') ⊛ᶜ δ' +ᶜ p ·ᶜ η' ▷ r                                 ≡˘⟨ cong (λ γ → (γ' ∧ᶜ _) ⊛ᶜ _ +ᶜ γ ▷ _) $
                                                                         update-distrib-·ᶜ _ _ _ _ ⟩

     (γ' ∧ᶜ η') ⊛ᶜ δ' +ᶜ pη' ▷ r                                     ≡˘⟨ cong (λ γ → (γ' ∧ᶜ _) ⊛ᶜ _ +ᶜ (_ , _ ≔ γ) ▷ _) $
                                                                         lookup-distrib-·ᶜ η′ _ _ ⟩

     (γ' ∧ᶜ η') ⊛ᶜ δ' +ᶜ (p ·ᶜ η , x ≔ (p ·ᶜ η′) ⟨ x ⟩) ▷ r          ≡˘⟨ cong (λ γ → (γ' ∧ᶜ _) ⊛ᶜ γ ▷ _) $
                                                                         update-distrib-+ᶜ _ _ _ _ _ ⟩

     (γ' ∧ᶜ η') ⊛ᶜ δ +ᶜ p ·ᶜ η , x ≔ δ′ ⟨ x ⟩ + (p ·ᶜ η′) ⟨ x ⟩ ▷ r  ≡˘⟨ cong₂ (λ γ δ → γ ⊛ᶜ _ , _ ≔ δ ▷ _)
                                                                           (update-distrib-∧ᶜ _ _ _ _ _)
                                                                           (lookup-distrib-+ᶜ δ′ _ _)   ⟩
     (γ ∧ᶜ η , x ≔ γ′ ⟨ x ⟩ ∧ η′ ⟨ x ⟩) ⊛ᶜ
     δ +ᶜ p ·ᶜ η , x ≔ (δ′ +ᶜ p ·ᶜ η′) ⟨ x ⟩ ▷ r                     ≡˘⟨ update-distrib-⊛ᶜ _ _ _ _ _ _ ⟩

     (γ ∧ᶜ η) ⊛ᶜ δ +ᶜ p ·ᶜ η ▷ r ,
     x ≔ (γ′ ⟨ x ⟩ ∧ η′ ⟨ x ⟩) ⊛ (δ′ +ᶜ p ·ᶜ η′) ⟨ x ⟩ ▷ r           ≡˘⟨ cong (λ p → _ , _ ≔ p ⊛ _ ▷ _) $
                                                                         lookup-distrib-∧ᶜ γ′ _ _ ⟩
     (γ ∧ᶜ η) ⊛ᶜ δ +ᶜ p ·ᶜ η ▷ r ,
     x ≔ (γ′ ∧ᶜ η′) ⟨ x ⟩ ⊛ (δ′ +ᶜ p ·ᶜ η′) ⟨ x ⟩ ▷ r                ≡˘⟨ cong (_ , _ ≔_) $
                                                                         lookup-distrib-⊛ᶜ (γ′ ∧ᶜ _) _ _ _ ⟩
     (γ ∧ᶜ η) ⊛ᶜ δ +ᶜ p ·ᶜ η ▷ r ,
     x ≔ ((γ′ ∧ᶜ η′) ⊛ᶜ δ′ +ᶜ p ·ᶜ η′ ▷ r) ⟨ x ⟩                     ∎) }
  where
  open import Graded.Modality.Dedicated-star.Instance
  open Tools.Reasoning.PropositionalEquality

  γ'  = γ , x ≔ γ′ ⟨ x ⟩
  δ'  = δ , x ≔ δ′ ⟨ x ⟩
  η'  = η , x ≔ η′ ⟨ x ⟩
  pη' = p ·ᶜ η , x ≔ p · η′ ⟨ x ⟩

Conₘ-interchange
  (natrec-no-starₘ {γ = γ} {δ = δ} {p = p} {r = r} {η = η} {χ = χ}
     ⦃ no-star = ns ⦄ γ▸z δ▸s η▸n θ▸A fix)
  (natrec-no-starₘ {γ = γ′} {δ = δ′} {η = η′} {χ = χ′}
     γ′▸z δ′▸s η′▸n _ fix′)
  x =
  natrec-no-starₘ ⦃ no-star = ns ⦄
    (Conₘ-interchange γ▸z γ′▸z x)
    (Conₘ-interchange δ▸s δ′▸s (x +1 +1))
    (Conₘ-interchange η▸n η′▸n x)
    θ▸A
    (begin
       χ , x ≔ χ′ ⟨ x ⟩                                      ≤⟨ update-monotone _ fix (lookup-monotone _ fix′) ⟩

       (γ ∧ᶜ η ∧ᶜ (δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ χ)) ,
       x ≔ (γ′ ∧ᶜ η′ ∧ᶜ (δ′ +ᶜ p ·ᶜ η′ +ᶜ r ·ᶜ χ′)) ⟨ x ⟩    ≈⟨ update-congʳ $
                                                                trans (lookup-distrib-∧ᶜ γ′ _ _) $
                                                                cong (_ ∧_) $
                                                                trans (lookup-distrib-∧ᶜ η′ _ _) $
                                                                cong (_ ∧_) $
                                                                trans (lookup-distrib-+ᶜ δ′ _ _) $
                                                                cong (_ +_) $
                                                                trans (lookup-distrib-+ᶜ (_ ·ᶜ η′) _ _) $
                                                                cong₂ _+_
                                                                  (lookup-distrib-·ᶜ η′ _ _)
                                                                  (lookup-distrib-·ᶜ χ′ _ _) ⟩
       (γ ∧ᶜ η ∧ᶜ (δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ χ)) ,
       x ≔ γ′ ⟨ x ⟩ ∧ η′ ⟨ x ⟩ ∧
           (δ′ ⟨ x ⟩ + p · η′ ⟨ x ⟩ + r · χ′ ⟨ x ⟩)          ≡⟨ trans (update-distrib-∧ᶜ _ _ _ _ _) $
                                                                cong (_ ∧ᶜ_) $
                                                                trans (update-distrib-∧ᶜ _ _ _ _ _) $
                                                                cong (_ ∧ᶜ_) $
                                                                trans (update-distrib-+ᶜ _ _ _ _ _) $
                                                                cong (_ +ᶜ_) $
                                                                trans (update-distrib-+ᶜ _ _ _ _ _) $
                                                                cong₂ _+ᶜ_
                                                                  (update-distrib-·ᶜ _ _ _ _)
                                                                  (update-distrib-·ᶜ _ _ _ _) ⟩
       (γ , x ≔ γ′ ⟨ x ⟩) ∧ᶜ
       (η , x ≔ η′ ⟨ x ⟩) ∧ᶜ
       ((δ , x ≔ δ′ ⟨ x ⟩) +ᶜ
        p ·ᶜ (η , x ≔ η′ ⟨ x ⟩) +ᶜ r ·ᶜ (χ , x ≔ χ′ ⟨ x ⟩))  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

Conₘ-interchange (natrecₘ _ _ _ _) (natrec-no-starₘ _ _ _ _ _) _ =
  ⊥-elim not-star-and-no-star

Conₘ-interchange (natrec-no-starₘ _ _ _ _ _) (natrecₘ _ _ _ _) _ =
  ⊥-elim not-star-and-no-star

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

Conₘ-interchange starₘ starₘ x =
  subst (_▸[ _ ] _) (PE.sym (update-self 𝟘ᶜ x)) starₘ

------------------------------------------------------------------------
-- Some lemmas related to natrec

-- The context used in the usage rule for natrec satisfies the neccessary inequalities
-- (γ ∧ η) ⊛ᶜ (δ + pη) ▷ r ≤ γ and
-- (γ ∧ η) ⊛ᶜ (δ + pη) ▷ r ≤ δ + pη + r ((γ ∧ η) ⊛ᶜ (δ + pη) ▷ r) and
-- (γ ∧ η) ⊛ᶜ (δ + pη) ▷ r ≤ η

natrec-usage :
  ⦃ has-star : Has-star semiring-with-meet ⦄ →
  (γ ∧ᶜ η) ⊛ᶜ (δ +ᶜ p ·ᶜ η) ▷ r ≤ᶜ γ ×
  (γ ∧ᶜ η) ⊛ᶜ (δ +ᶜ p ·ᶜ η) ▷ r ≤ᶜ
    δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ (γ ∧ᶜ η) ⊛ᶜ (δ +ᶜ p ·ᶜ η) ▷ r ×
  (γ ∧ᶜ η) ⊛ᶜ (δ +ᶜ p ·ᶜ η) ▷ r ≤ᶜ η
natrec-usage {γ = γ} {η} {δ} {p} {r} =
  ≤ᶜ-trans (⊛ᶜ-ineq₂ (γ ∧ᶜ η) (δ +ᶜ p ·ᶜ η) r) (∧ᶜ-decreasingˡ γ η)
  , ≤ᶜ-trans (⊛ᶜ-ineq₁ (γ ∧ᶜ η) (δ +ᶜ p ·ᶜ η) r)
             (≤ᶜ-reflexive (+ᶜ-assoc δ (p ·ᶜ η) (r ·ᶜ (γ ∧ᶜ η) ⊛ᶜ (δ +ᶜ p ·ᶜ η) ▷ r)))
  , ≤ᶜ-trans (⊛ᶜ-ineq₂ (γ ∧ᶜ η) (δ +ᶜ p ·ᶜ η) r) (∧ᶜ-decreasingʳ γ η)

-- A variant of natrec-no-starₘ.

natrec-no-star-⊛ₘ :
  ⦃ no-star : No-dedicated-star ⦄
  ⦃ has-star : Has-star semiring-with-meet ⦄ →
  γ ▸[ m ] t →
  δ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · r ▸[ m ] u →
  η ▸[ m ] v →
  θ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] A →
  (γ ∧ᶜ η) ⊛ᶜ (δ +ᶜ p ·ᶜ η) ▷ r ▸[ m ] natrec p q r A t u v
natrec-no-star-⊛ₘ ▸t ▸u ▸v ▸A =
  natrec-no-starₘ ▸t ▸u ▸v ▸A
    (∧ᶜ-greatest-lower-bound
       (natrec-usage .proj₁)
       (∧ᶜ-greatest-lower-bound
          (natrec-usage .proj₂ .proj₂)
          (natrec-usage .proj₂ .proj₁)))

module _ where

  open import Graded.Modality.Dedicated-star.Instance

  -- A variant of natrecₘ and natrec-no-starₘ.

  natrec-star-or-no-starₘ :
    γ ▸[ m ] t →
    δ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · r ▸[ m ] u →
    η ▸[ m ] v →
    θ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] A →
    (⦃ has-star : Dedicated-star ⦄ →
     χ ≤ᶜ (γ ∧ᶜ η) ⊛ᶜ (δ +ᶜ p ·ᶜ η) ▷ r) →
    (⦃ no-star : No-dedicated-star ⦄ →
     χ ≤ᶜ γ ∧ᶜ η ∧ᶜ (δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ χ)) →
    χ ▸[ m ] natrec p q r A t u v
  natrec-star-or-no-starₘ ▸t ▸u ▸v ▸A hyp₁ hyp₂ =
    case dedicated-star? of λ where
      does-have-star →
        sub (natrecₘ ▸t ▸u ▸v ▸A) hyp₁
      does-not-have-star →
        natrec-no-starₘ ▸t ▸u ▸v ▸A hyp₂

------------------------------------------------------------------------
-- Lemmas related to ⌈_⌉

-- The context ⌈ t ⌉ 𝟘ᵐ[ ok ] is equivalent to 𝟘ᶜ.

⌈⌉-𝟘ᵐ :
  ⦃ has-star : Has-star semiring-with-meet ⦄ →
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
⌈⌉-𝟘ᵐ {ok = ok} (prod Σᵣ p t u) = begin
  p ·ᶜ ⌈ t ⌉ 𝟘ᵐ[ ok ] +ᶜ ⌈ u ⌉ 𝟘ᵐ[ ok ]  ≈⟨ +ᶜ-cong (·ᶜ-congˡ (⌈⌉-𝟘ᵐ t)) (⌈⌉-𝟘ᵐ u) ⟩
  p ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ                          ≈⟨ +ᶜ-identityʳ _ ⟩
  p ·ᶜ 𝟘ᶜ                                ≈⟨ ·ᶜ-zeroʳ _ ⟩
  𝟘ᶜ                                     ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid
⌈⌉-𝟘ᵐ {ok = ok} (prod Σₚ p t u) = begin
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
⌈⌉-𝟘ᵐ ℕ =
  ≈ᶜ-refl
⌈⌉-𝟘ᵐ zero =
  ≈ᶜ-refl
⌈⌉-𝟘ᵐ (suc t) =
  ⌈⌉-𝟘ᵐ t
⌈⌉-𝟘ᵐ {ok = ok} (natrec p _ r A z s n) = begin
  (⌈ z ⌉ 𝟘ᵐ[ ok ] ∧ᶜ ⌈ n ⌉ 𝟘ᵐ[ ok ]) ⊛ᶜ
    tailₘ (tailₘ (⌈ s ⌉ 𝟘ᵐ[ ok ])) +ᶜ p ·ᶜ ⌈ n ⌉ 𝟘ᵐ[ ok ] ▷ r  ≈⟨ ⊛ᵣᶜ-cong (∧ᶜ-cong (⌈⌉-𝟘ᵐ z) (⌈⌉-𝟘ᵐ n))
                                                                    (+ᶜ-cong (tailₘ-cong (tailₘ-cong (⌈⌉-𝟘ᵐ s)))
                                                                       (·ᶜ-congˡ (⌈⌉-𝟘ᵐ n))) ⟩
  (𝟘ᶜ ∧ᶜ 𝟘ᶜ) ⊛ᶜ 𝟘ᶜ +ᶜ p ·ᶜ 𝟘ᶜ ▷ r                              ≈⟨ ⊛ᵣᶜ-cong (∧ᶜ-idem _) (+ᶜ-identityˡ _) ⟩
  𝟘ᶜ ⊛ᶜ p ·ᶜ 𝟘ᶜ ▷ r                                            ≈⟨ ⊛ᵣᶜ-congˡ (·ᶜ-zeroʳ _) ⟩
  𝟘ᶜ ⊛ᶜ 𝟘ᶜ ▷ r                                                 ≈⟨ ⊛ᶜ-idem-𝟘ᶜ _ ⟩
  𝟘ᶜ                                                           ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid
⌈⌉-𝟘ᵐ Unit =
  ≈ᶜ-refl
⌈⌉-𝟘ᵐ star =
  ≈ᶜ-refl
⌈⌉-𝟘ᵐ Empty =
  ≈ᶜ-refl
⌈⌉-𝟘ᵐ {ok = ok} (emptyrec p _ t) = begin
  p ·ᶜ ⌈ t ⌉ 𝟘ᵐ[ ok ]  ≈⟨ ·ᶜ-congˡ (⌈⌉-𝟘ᵐ t) ⟩
  p ·ᶜ 𝟘ᶜ              ≈⟨ ·ᶜ-zeroʳ _ ⟩
  𝟘ᶜ                   ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid

-- The context ⌈ t ⌉ m does not change (up to _≈ᶜ_) if it is
-- multiplied by ⌜ m ⌝.

·-⌈⌉ :
  ⦃ has-star : Has-star semiring-with-meet ⦄ →
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

open import Graded.Modality.Dedicated-star.Instance

-- For dedicated natrec-star operators the function ⌈_⌉ provides upper
-- bounds for valid modality contexts: if γ ▸[ m ] t, then
-- γ ≤ᶜ ⌈ t ⌉ m.

usage-upper-bound :
  ⦃ has-star : Dedicated-star ⦄ →
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

usage-upper-bound (prodᵣₘ t u) =
  +ᶜ-monotone (·ᶜ-monotoneʳ (usage-upper-bound t)) (usage-upper-bound u)
usage-upper-bound (prodₚₘ t u) =
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
  ⦃ has-star = s₁ ⦄
  (natrecₘ {z = z} {s = s} {n = n} ⦃ has-star = s₂ ⦄ γ▸z δ▸s η▸n θ▸A) =
  case Dedicated-star-propositional s₁ s₂ of λ {
    refl →
  case usage-upper-bound γ▸z of λ {
    γ≤γ′ →
  case usage-upper-bound δ▸s of λ {
    δ≤δ′ →
  case usage-upper-bound η▸n of λ {
    η≤η′ →
  ⊛ᶜ-monotone (∧ᶜ-monotone γ≤γ′ η≤η′)
               (+ᶜ-monotone (tailₘ-monotone (tailₘ-monotone δ≤δ′))
                            (·ᶜ-monotoneʳ η≤η′)) }}}}

usage-upper-bound (natrec-no-starₘ _ _ _ _ _) =
  ⊥-elim not-star-and-no-star

usage-upper-bound (emptyrecₘ e A) =
  ·ᶜ-monotoneʳ (usage-upper-bound e)
usage-upper-bound starₘ = ≤ᶜ-refl
usage-upper-bound (sub t x) = ≤ᶜ-trans x (usage-upper-bound t)


-- A valid modality context can be computed from a well-resourced
-- term (if there is a dedicated natrec-star operator).

usage-inf :
  ⦃ has-star : Dedicated-star ⦄ →
  γ ▸[ m ] t → ⌈ t ⌉ m ▸[ m ] t
usage-inf Uₘ = Uₘ
usage-inf ℕₘ = ℕₘ
usage-inf Emptyₘ = Emptyₘ
usage-inf Unitₘ = Unitₘ
usage-inf (ΠΣₘ {G = G} γ▸F δ▸G) =
  ΠΣₘ (usage-inf γ▸F)
      (sub (usage-inf δ▸G)
           (subst (tailₘ (⌈ G ⌉ _) ∙ _ ≤ᶜ_)
                  (headₘ-tailₘ-correct (⌈ G ⌉ _))
                  (≤ᶜ-refl ∙ headₘ-monotone (usage-upper-bound δ▸G))))
usage-inf var = var
usage-inf (lamₘ {p = p} {t = t} γ▸t) =
  lamₘ (sub (usage-inf γ▸t)
            (PE.subst (⌈ lam p t ⌉ _ ∙ _ ≤ᶜ_)
                      (headₘ-tailₘ-correct (⌈ t ⌉ _))
                      (≤ᶜ-refl ∙ headₘ-monotone (usage-upper-bound γ▸t))))
usage-inf (γ▸t ∘ₘ γ▸t₁) = usage-inf γ▸t ∘ₘ usage-inf γ▸t₁
usage-inf (prodᵣₘ γ▸t γ▸t₁) = prodᵣₘ (usage-inf γ▸t) (usage-inf γ▸t₁)
usage-inf (prodₚₘ γ▸t γ▸t₁) = prodₚₘ (usage-inf γ▸t) (usage-inf γ▸t₁)
usage-inf (fstₘ m γ▸t PE.refl ok) =
  fstₘ m (usage-inf γ▸t) PE.refl ok
usage-inf (sndₘ γ▸t) = sndₘ (usage-inf γ▸t)
usage-inf (prodrecₘ {p = p} {u = u} γ▸t δ▸u η▸A ok) =
  prodrecₘ (usage-inf γ▸t)
           (sub (usage-inf δ▸u)
                (subst (tailₘ (tailₘ (⌈ u ⌉ _)) ∙ _ ∙ _ ≤ᶜ_)
                       (PE.trans
                          (cong (_∙ headₘ (⌈ u ⌉ _))
                             (headₘ-tailₘ-correct (tailₘ (⌈ u ⌉ _))))
                          (headₘ-tailₘ-correct (⌈ u ⌉ _)))
                       (≤ᶜ-refl ∙ headₘ-monotone (tailₘ-monotone (usage-upper-bound δ▸u)) ∙ headₘ-monotone (usage-upper-bound δ▸u))))
           η▸A
           ok
usage-inf zeroₘ = zeroₘ
usage-inf (sucₘ γ▸t) = sucₘ (usage-inf γ▸t)
usage-inf
  ⦃ has-star = s₁ ⦄
  (natrecₘ {p = p} {r = r} {s = s} ⦃ has-star = s₂ ⦄ γ▸z δ▸s η▸n θ▸A) =
  case Dedicated-star-propositional s₁ s₂ of λ {
    refl →
  natrecₘ (usage-inf γ▸z)
          (sub (usage-inf δ▸s)
               (subst (tailₘ (tailₘ (⌈ s ⌉ _)) ∙ _ ∙ _ ≤ᶜ_)
                      (PE.trans
                         (cong (_∙ headₘ (⌈ s ⌉ _))
                            (headₘ-tailₘ-correct (tailₘ (⌈ s ⌉ _))))
                         (headₘ-tailₘ-correct (⌈ s ⌉ _)))
                      (≤ᶜ-refl ∙ headₘ-monotone (tailₘ-monotone (usage-upper-bound δ▸s)) ∙ headₘ-monotone (usage-upper-bound δ▸s))))
          (usage-inf η▸n)
          θ▸A }
usage-inf (natrec-no-starₘ _ _ _ _ _) =
  ⊥-elim not-star-and-no-star
usage-inf (emptyrecₘ γ▸t δ▸A) = emptyrecₘ (usage-inf γ▸t) δ▸A
usage-inf starₘ = starₘ
usage-inf (sub γ▸t x) = usage-inf γ▸t

------------------------------------------------------------------------
-- A negative result

module _ (TR : Type-restrictions) where

  open Definition.Typed TR

  -- It is always the case that Γ ⊢ t ∷ A implies Γ ⊢ A (see
  -- Definition.Typed.Consequences.Syntactic.syntacticTerm), but if
  -- 𝟙 ≢ 𝟘, then it is not necessarily the case that Γ ⊢ t ∷ A and
  -- γ ▸[ 𝟙ᵐ ] t imply γ ▸[ 𝟙ᵐ ] A.

  ▸-term→▸-type :
    𝟙 ≢ 𝟘 →
    ¬ (∀ {n} {Γ : Con Term n} {t A : Term n} {γ : Conₘ n} →
       Γ ⊢ t ∷ A → γ ▸[ 𝟙ᵐ ] t → γ ▸[ 𝟙ᵐ ] A)
  ▸-term→▸-type 𝟙≢𝟘 hyp =
    case inv-usage-var (hyp ⊢t ▸t) of λ {
      (ε ∙ 𝟘≤𝟙 ∙ 𝟙≤𝟘) →
    𝟙≢𝟘 (≤-antisym 𝟙≤𝟘 𝟘≤𝟙) }
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
