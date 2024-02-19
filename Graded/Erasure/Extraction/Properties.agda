------------------------------------------------------------------------
-- Properties of the extraction function.
------------------------------------------------------------------------

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
open import Graded.Erasure.Target as T hiding (refl; trans)
open import Graded.Erasure.Target.Properties.Substitution

open import Definition.Untyped M as U
  hiding (Term; wk; _[_]; _[_,_]; liftSubst)

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

-- Lemmata on how erase computes

prod-𝟘 : p PE.≡ 𝟘
       → erase (U.prod k p t u) PE.≡ erase u
prod-𝟘 {p = p} p≡𝟘 with is-𝟘? p
... | yes p≡𝟘 = PE.refl
... | no p≢𝟘 = ⊥-elim (p≢𝟘 p≡𝟘)

prod-ω : p PE.≢ 𝟘
       → erase (U.prod k p t u) PE.≡ T.prod (erase t) (erase u)
prod-ω {p = p} p≢𝟘 with is-𝟘? p
... | yes p≡𝟘 = ⊥-elim (p≢𝟘 p≡𝟘)
... | no p≢𝟘 = PE.refl

snd-𝟘 : p PE.≡ 𝟘
      → erase (U.snd p t) PE.≡ erase t
snd-𝟘 {p = p} p≡𝟘 with is-𝟘? p
... | yes p≡𝟘 = PE.refl
... | no p≢𝟘 = ⊥-elim (p≢𝟘 p≡𝟘)

snd-ω : p PE.≢ 𝟘
      → erase (U.snd p t) PE.≡ T.snd (erase t)
snd-ω {p = p} p≢𝟘 with is-𝟘? p
... | yes p≡𝟘 = ⊥-elim (p≢𝟘 p≡𝟘)
... | no p≢𝟘 = PE.refl

prodrec-ω : ∀ p → r PE.≢ 𝟘
          → erase (U.prodrec r p q A t u)
          PE.≡ erase-prodrecω p (erase t) (erase u)
prodrec-ω {r} p r≢𝟘 with is-𝟘? r
... | yes r≡𝟘 = ⊥-elim (r≢𝟘 r≡𝟘)
... | no r≢𝟘 with is-𝟘? p
... | yes p≡𝟘 = PE.refl
... | no p≢𝟘 = PE.refl

-- The functions wk ρ/U.wk ρ and erase commute.

wk-erase-comm : (ρ : U.Wk m n) (t : U.Term n)
              → wk ρ (erase t) ≡ erase (U.wk ρ t)
wk-erase-comm _ (var _) = refl
wk-erase-comm ρ U = refl
wk-erase-comm ρ (Π p , w ▷ F ▹ G) = refl
wk-erase-comm ρ (U.lam p t) =
  cong T.lam (wk-erase-comm (lift ρ) t)
wk-erase-comm ρ (t ∘⟨ p ⟩ u) with is-𝟘? p
... | yes _ = cong (T._∘ ↯) (wk-erase-comm ρ t)
... | no _ = cong₂ T._∘_ (wk-erase-comm ρ t) (wk-erase-comm ρ u)
wk-erase-comm ρ (Σ _ , _ ▷ _ ▹ _) = refl
wk-erase-comm ρ (U.prod _ p t u) with is-𝟘? p
... | yes _ = wk-erase-comm ρ u
... | no _ = cong₂ T.prod (wk-erase-comm ρ t) (wk-erase-comm ρ u)
wk-erase-comm ρ (U.fst p t) with is-𝟘? p
... | yes _ = refl
... | no _ = cong T.fst (wk-erase-comm ρ t)
wk-erase-comm ρ (U.snd p t) with is-𝟘? p
... | yes _ = wk-erase-comm ρ t
... | no _ = cong T.snd (wk-erase-comm ρ t)
wk-erase-comm ρ (U.prodrec r p _ A t u) with is-𝟘? r
... | yes _ = cong (Term.prodrec (Term.prod ↯ ↯))
                   (wk-erase-comm (lift (lift ρ)) u)
... | no _ with is-𝟘? p
... | yes _ =
  T.prodrec (T.prod ↯ (wk ρ (erase t)))
    (wk (lift (lift ρ)) (erase u))         ≡⟨ cong₂ (λ t u → T.prodrec (T.prod ↯ t) u)
                                                (wk-erase-comm _ t)
                                                (wk-erase-comm _ u) ⟩
  T.prodrec (T.prod ↯ (erase (U.wk ρ t)))
    (erase (U.wk (lift (lift ρ)) u))       ∎
  where
  open Tools.Reasoning.PropositionalEquality
... | no _ = cong₂ T.prodrec (wk-erase-comm ρ t)
                   (wk-erase-comm (lift (lift ρ)) u)
wk-erase-comm ρ ℕ = refl
wk-erase-comm ρ U.zero = refl
wk-erase-comm ρ (U.suc t) =
  cong T.suc (wk-erase-comm ρ t)
wk-erase-comm ρ (U.natrec p q r A z s n) =
  cong₃ T.natrec (wk-erase-comm ρ z)
                 (wk-erase-comm (lift (lift ρ)) s)
                 (wk-erase-comm ρ n)
wk-erase-comm ρ Unit! = refl
wk-erase-comm ρ U.star! = refl
wk-erase-comm ρ (U.unitrec p q A t u)
  with is-𝟘? p
... | yes _ =
  cong (T.unitrec T.star) (wk-erase-comm ρ u)
... | no _ =
  cong₂ T.unitrec (wk-erase-comm ρ t)
                  (wk-erase-comm ρ u)
wk-erase-comm ρ Empty = refl
wk-erase-comm ρ (emptyrec p A t) = refl
wk-erase-comm _ (Id _ _ _) = refl
wk-erase-comm _ U.rfl = refl
wk-erase-comm _ (J _ _ _ _ _ u _ _) = wk-erase-comm _ u
wk-erase-comm _ (K _ _ _ _ u _) = wk-erase-comm _ u
wk-erase-comm _ ([]-cong _ _ _ _ _) = refl

-- Lifting substitutions commute with erase
-- liftSubst (eraseSubst σ) x ≡ eraseSubst (liftSubst σ) x

liftSubst-erase-comm : (x : Fin (1+ n))
                     → liftSubst (eraseSubst σ) x ≡ eraseSubst (U.liftSubst σ) x
liftSubst-erase-comm x0 = refl
liftSubst-erase-comm {σ = σ} (x +1) with σ x
... | var x₁ = refl
... | U = refl
... | Π p , q ▷ F ▹ G = refl
... | U.lam p t =
  cong T.lam (wk-erase-comm (lift (step id)) t)
... | t ∘⟨ p ⟩ u with is-𝟘? p
... | yes _ = cong (T._∘ ↯) (wk-erase-comm (step id) t)
... | no _ = cong₂ T._∘_ (wk-erase-comm (step id) t)
                         (wk-erase-comm (step id) u)
liftSubst-erase-comm (x +1) | ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _ = refl
liftSubst-erase-comm (x +1) | U.prod _ p t u with is-𝟘? p
... | yes _ = wk-erase-comm (step id) u
... | no _ = cong₂ T.prod (wk-erase-comm (step id) t)
                          (wk-erase-comm (step id) u)
liftSubst-erase-comm (x +1) | U.fst p t with is-𝟘? p
... | yes _ = refl
... | no _ = cong T.fst (wk-erase-comm (step id) t)
liftSubst-erase-comm (x +1) | U.snd p t with is-𝟘? p
... | yes _ = wk-erase-comm (step id) t
... | no _ = cong T.snd (wk-erase-comm (step id) t)
liftSubst-erase-comm (x +1) | U.prodrec r p _ A t u with is-𝟘? r
... | yes r≡𝟘 = cong (Term.prodrec (Term.prod ↯ ↯))
                   (wk-erase-comm (lift (lift (step id))) u)
... | no r≢𝟘 with is-𝟘? p
... | yes p≡𝟘 = cong₂ (λ t u → Term.prodrec (Term.prod ↯ t) u)
                      (wk-erase-comm (step id) t)
                      (wk-erase-comm _ u)
... | no _ =
  cong₂ Term.prodrec (wk-erase-comm (step id) t)
                     (wk-erase-comm (lift (lift (step id))) u)
liftSubst-erase-comm (x +1) | ℕ = refl
liftSubst-erase-comm (x +1) | U.zero = refl
liftSubst-erase-comm (x +1) | U.suc t = cong T.suc (wk-erase-comm (step id) t)
liftSubst-erase-comm (x +1) | U.natrec p q r A z s n =
  cong₃ T.natrec (wk-erase-comm (step id) z)
                 (wk-erase-comm (lift (lift (step id))) s)
                 (wk-erase-comm (step id) n)
liftSubst-erase-comm (x +1) | Unit! = refl
liftSubst-erase-comm (x +1) | U.star! = refl
liftSubst-erase-comm (x +1) | U.unitrec p q A t u with is-𝟘? p
... | yes _ =
  cong (T.unitrec T.star) (wk-erase-comm (step id) u)
... | no _ =
  cong₂ Term.unitrec (wk-erase-comm (step id) t)
                     (wk-erase-comm (step id) u)
liftSubst-erase-comm (x +1) | Empty = refl
liftSubst-erase-comm (x +1) | emptyrec p A t = refl
liftSubst-erase-comm _      | Id _ _ _ = refl
liftSubst-erase-comm _      | U.rfl = refl
liftSubst-erase-comm _      | J _ _ _ _ _ u _ _ = wk-erase-comm _ u
liftSubst-erase-comm _      | K _ _ _ _ u _ = wk-erase-comm _ u
liftSubst-erase-comm _      | []-cong _ _ _ _ _ = refl

-- Multiple lifts commutes with erase
-- liftSubstn (eraseSubst σ) n x ≡ eraseSubst (liftSubstn σ n) x

liftSubsts-erase-comm : (k : Nat) (x : Fin (k +ⁿ n))
                      → T.liftSubstn (eraseSubst σ) k x ≡ eraseSubst (U.liftSubstn σ k) x
liftSubsts-erase-comm 0 x = refl
liftSubsts-erase-comm (1+ k) x0 = refl
liftSubsts-erase-comm {σ = σ} (1+ k) (x +1) = begin
  T.wk1 (T.liftSubstn (eraseSubst σ) k x)
    ≡⟨ cong T.wk1 (liftSubsts-erase-comm k x) ⟩
  T.wk1 (eraseSubst (U.liftSubstn σ k) x)
    ≡⟨⟩
  wk (step id) (eraseSubst (U.liftSubstn σ k) x)
    ≡⟨ wk-erase-comm (U.step U.id) (U.liftSubstn σ k x) ⟩
  erase (U.wk (U.step U.id) (U.liftSubstn σ k x))
    ≡⟨⟩
  eraseSubst (U.liftSubstn σ (1+ k)) (x +1)       ∎
  where open import Tools.Reasoning.PropositionalEquality


-- Substitution commutes with erase (modulo translating substitution to target language)
-- erase t [ eraseSubst σ ] ≡ erase (t [ σ ])

subst-erase-comm : (σ : U.Subst m n) (t : U.Term n)
                 → erase t T.[ eraseSubst σ ] ≡ erase (t U.[ σ ])
subst-erase-comm σ (var x) = refl
subst-erase-comm σ U = refl
subst-erase-comm σ (Π p , q ▷ F ▹ G) = refl
subst-erase-comm σ (U.lam p t) =
  cong Term.lam
    (begin
      erase t T.[ liftSubst (eraseSubst σ) ]
        ≡⟨ substVar-to-subst (liftSubsts-erase-comm 1) (erase t) ⟩
      erase t T.[ eraseSubst (U.liftSubst σ) ]
        ≡⟨ subst-erase-comm (U.liftSubst σ) t ⟩
      erase (t U.[ U.liftSubst σ ]) ∎)
  where open import Tools.Reasoning.PropositionalEquality
subst-erase-comm σ (t ∘⟨ p ⟩ u) with is-𝟘? p
... | yes _ = cong (T._∘ ↯) (subst-erase-comm σ t)
... | no _ = cong₂ T._∘_ (subst-erase-comm σ t) (subst-erase-comm σ u)
subst-erase-comm σ (ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _) = refl
subst-erase-comm σ (U.prod _ p t u) with is-𝟘? p
... | yes _ = subst-erase-comm σ u
... | no _ = cong₂ T.prod (subst-erase-comm σ t) (subst-erase-comm σ u)
subst-erase-comm σ (U.fst p t) with is-𝟘? p
... | yes _ = refl
... | no _ = cong T.fst (subst-erase-comm σ t)
subst-erase-comm σ (U.snd p t) with is-𝟘? p
... | yes _ = subst-erase-comm σ t
... | no _  = cong T.snd (subst-erase-comm σ t)
subst-erase-comm σ (U.prodrec r p _ A t u) with is-𝟘? r
... | yes _ =
  cong (Term.prodrec (Term.prod ↯ ↯))
       (trans (substVar-to-subst (liftSubsts-erase-comm 2) (erase u))
              (subst-erase-comm (U.liftSubstn σ 2) u))
... | no _ with is-𝟘? p
... | yes _ =
  T.prodrec (T.prod ↯ (erase t T.[ eraseSubst σ ]))
    (erase u T.[ T.liftSubstn (eraseSubst σ) 2 ])    ≡⟨ cong (T.prodrec (T.prod ↯ (erase t T.[ eraseSubst σ ])))
                                                             (substVar-to-subst (liftSubsts-erase-comm 2) (erase u)) ⟩
  T.prodrec (T.prod ↯ (erase t T.[ eraseSubst σ ]))
    (erase u T.[ eraseSubst (U.liftSubstn σ 2) ])    ≡⟨ cong₂ (λ t u → T.prodrec (T.prod ↯ t) u)
                                                                       (subst-erase-comm _ t)
                                                                       (subst-erase-comm _ u) ⟩
  T.prodrec (T.prod ↯ (erase (t U.[ σ ])))
    (erase (u U.[ U.liftSubstn σ 2 ]))               ∎
  where
  open Tools.Reasoning.PropositionalEquality
... | no _ =
  cong₂ Term.prodrec (subst-erase-comm σ t)
        (trans (substVar-to-subst (liftSubsts-erase-comm 2) (erase u))
               (subst-erase-comm (U.liftSubstn σ 2) u))
subst-erase-comm σ ℕ = refl
subst-erase-comm σ U.zero = refl
subst-erase-comm σ (U.suc t) = cong T.suc (subst-erase-comm σ t)
subst-erase-comm σ (U.natrec p q r A z s n) = cong₃ T.natrec
  (subst-erase-comm σ z)
  (trans (substVar-to-subst (liftSubsts-erase-comm 2) (erase s))
         (subst-erase-comm (U.liftSubst (U.liftSubst σ)) s))
  (subst-erase-comm σ n)
subst-erase-comm σ Unit! = refl
subst-erase-comm σ U.star! = refl
subst-erase-comm σ (U.unitrec p q A t u) with is-𝟘? p
... | yes _ =
  cong (T.unitrec T.star) (subst-erase-comm σ u)
... | no _ =
  cong₂ T.unitrec (subst-erase-comm σ t)
                  (subst-erase-comm σ u)
subst-erase-comm σ Empty = refl
subst-erase-comm σ (emptyrec p A t) = refl
subst-erase-comm _ (Id _ _ _) = refl
subst-erase-comm _ U.rfl = refl
subst-erase-comm _ (J _ _ _ _ _ u _ _) = subst-erase-comm _ u
subst-erase-comm _ (K _ _ _ _ u _) = subst-erase-comm _ u
subst-erase-comm _ ([]-cong _ _ _ _ _) = refl

subst-undefined : (x : Fin (1+ n)) →
      eraseSubst (U.sgSubst Empty) x ≡
      T.sgSubst ↯ x
subst-undefined x0 = refl
subst-undefined (x +1) = refl

erase-consSubst-var : (σ : U.Subst m n) (a : U.Term m) (x : Fin (1+ n))
                    → T.consSubst (eraseSubst σ) (erase a) x
                    ≡ eraseSubst (U.consSubst σ a) x
erase-consSubst-var σ a x0 = refl
erase-consSubst-var σ a (x +1) = refl

erase-consSubst : (σ : U.Subst m n) (a : U.Term m) (t : T.Term (1+ n))
                → t T.[ T.consSubst (eraseSubst σ) (erase a) ]
                ≡ t T.[ eraseSubst (U.consSubst σ a) ]
erase-consSubst σ a t = substVar-to-subst (erase-consSubst-var σ a) t

module hasX (R : Usage-restrictions) where

  open MU R
  open MUP R
  open MUP𝟘 R

  -- Erased variables do not occur after extraction.
  --
  -- Proof by induction on t being well-resourced.

  erased-hasX : x ◂ 𝟘 ∈ γ → γ ▸[ 𝟙ᵐ ] t → HasX x (erase t) → ⊥

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
  erased-hasX erased (fstₘ {p = _} _ _ _ _) () | yes _
  erased-hasX erased (fstₘ {p = _} 𝟘ᵐ _ () _) (fstₓ hasX) | no _
  erased-hasX erased (fstₘ {p = _} 𝟙ᵐ γ▸ _ _) (fstₓ hasX) | no p≢𝟘 =
    erased-hasX erased (▸-cong (≢𝟘→⌞⌟≡𝟙ᵐ p≢𝟘) γ▸) hasX


  erased-hasX erased (sndₘ {p = p} γ▸) hasX with is-𝟘? p
  ... | yes _ = erased-hasX erased γ▸ hasX
  erased-hasX erased (sndₘ {p = _} γ▸) (sndₓ hasX) | no _ =
    erased-hasX erased γ▸ hasX

  erased-hasX erased (prodrecₘ {r = r} {p = p} ▸t ▸u _ _) hasX
    with is-𝟘? r
  erased-hasX erased (prodrecₘ ▸t ▸u _ _) (prodrecₓˡ (prodₓˡ ()))
    | yes _
  erased-hasX erased (prodrecₘ ▸t ▸u _ _) (prodrecₓˡ (prodₓʳ ()))
    | yes _
  erased-hasX erased (prodrecₘ ▸t ▸u _ _) (prodrecₓʳ hasX) | yes _ =
    erased-hasX (there (there (x◂𝟘∈γ+δʳ refl erased))) ▸u hasX
  ... | no _ with is-𝟘? p
  erased-hasX erased (prodrecₘ ▸t ▸u _ _)
              (prodrecₓˡ (prodₓʳ hasX)) | no r≢𝟘 | yes _ =
    erased-hasX (x◂𝟘∈pγ refl r≢𝟘 (x◂𝟘∈γ+δˡ refl erased))
                (▸-cong (≢𝟘→⌞⌟≡𝟙ᵐ r≢𝟘) ▸t) hasX
  erased-hasX erased (prodrecₘ ▸t ▸u _ _) (prodrecₓʳ hasX)
    | no _ | yes _ =
    erased-hasX (there (there (x◂𝟘∈γ+δʳ refl erased))) ▸u hasX
  erased-hasX erased (prodrecₘ ▸t ▸u _ _) (prodrecₓˡ hasX)
    | no r≢𝟘 | no _ =
    erased-hasX (x◂𝟘∈pγ refl r≢𝟘 (x◂𝟘∈γ+δˡ refl erased))
                (▸-cong (≢𝟘→⌞⌟≡𝟙ᵐ r≢𝟘) ▸t) hasX
  erased-hasX erased (prodrecₘ ▸t ▸u _ _) (prodrecₓʳ hasX)
    | no _ | no _ =
    erased-hasX (there (there (x◂𝟘∈γ+δʳ refl erased))) ▸u hasX

  erased-hasX erased (sucₘ γ▸t) (sucₓ hasX) =
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

  erased-hasX erased (Jₘ _ _ _ _ ▸u _ _) hasX =
    erased-hasX
      (x◂𝟘∈γ∧δˡ refl $ x◂𝟘∈γ∧δʳ refl $ x◂𝟘∈γ∧δʳ refl $
       x◂𝟘∈pγ refl ω≢𝟘 erased)
      ▸u hasX
  erased-hasX erased (Jₘ′ _ _ _ _ ▸u _ _) hasX =
    erased-hasX
      (x◂𝟘∈γ∧δˡ refl $ x◂𝟘∈γ∧δʳ refl $ x◂𝟘∈γ∧δʳ refl $
       x◂𝟘∈pγ refl ω≢𝟘 erased)
      ▸u hasX
  erased-hasX erased (J₀ₘ _ _ _ _ ▸u _ _) hasX =
    erased-hasX erased ▸u hasX
  erased-hasX erased (Kₘ _ _ _ _ ▸u _) hasX =
    erased-hasX
      (x◂𝟘∈γ∧δˡ refl $ x◂𝟘∈γ∧δʳ refl $ x◂𝟘∈γ∧δʳ refl $
       x◂𝟘∈pγ refl ω≢𝟘 erased)
      ▸u hasX
  erased-hasX erased (Kₘ′ _ _ _ _ ▸u _) hasX =
    erased-hasX
      (x◂𝟘∈γ∧δˡ refl $ x◂𝟘∈γ∧δʳ refl $ x◂𝟘∈γ∧δʳ refl $
       x◂𝟘∈pγ refl ω≢𝟘 erased)
      ▸u hasX
  erased-hasX erased (K₀ₘ _ _ _ _ ▸u _) hasX =
    erased-hasX erased ▸u hasX

  erased-hasX erased (unitrecₘ {p = p} γ▸t δ▸u η▸A ok) hasX
    with is-𝟘? p
  erased-hasX erased (unitrecₘ {p = _} γ▸t δ▸u η▸A ok) (unitrecₓʳ hasX) | yes _ =
    erased-hasX (x◂𝟘∈γ+δʳ refl erased) δ▸u hasX
  erased-hasX erased (unitrecₘ {p = _} γ▸t δ▸u η▸A ok) (unitrecₓˡ hasX) | no p≢𝟘 =
    erased-hasX (x◂𝟘∈pγ refl p≢𝟘 (x◂𝟘∈γ+δˡ refl erased))
                (▸-cong (≢𝟘→⌞⌟≡𝟙ᵐ p≢𝟘) γ▸t) hasX
  erased-hasX erased (unitrecₘ {p = _} γ▸t δ▸u η▸A ok) (unitrecₓʳ hasX) | no _ =
    erased-hasX (x◂𝟘∈γ+δʳ refl erased) δ▸u hasX

  erased-hasX erased (sub δ▸t γ≤δ) hasX =
    erased-hasX (x◂𝟘∈γ≤δ erased γ≤δ) δ▸t hasX
