{-# OPTIONS --without-K --safe #-}

open import Definition.Modality.Instances.Erasure

module Erasure.Extraction.Properties (Prodrec : Erasure → Set) where

open import Erasure.Extraction
open import Erasure.Target as T hiding (refl; trans)
open import Erasure.Target.Properties.Substitution

open import Definition.Modality.Instances.Erasure.Modality Prodrec
open import Definition.Modality.Instances.Erasure.Properties Prodrec
open import Definition.Untyped Erasure as U hiding (Wk; Term; wk; wkVar; _[_]; _[_,_]; liftSubst)

open import Definition.Modality.Context ErasureModality
open import Definition.Modality.Usage ErasureModality
open import Definition.Modality.Usage.Properties ErasureModality

open import Tools.Fin
open import Tools.Nat renaming (_+_ to _+ⁿ_)
open import Tools.PropositionalEquality as PE


private
  variable
    m n : Nat
    t : U.Term n
    σ : U.Subst m n
    γ : Conₘ n
    x : Fin n

-- Weakenings act the same on variables of both target and source languages
-- wkVar (eraseWk ρ) x ≡ wkVar ρ x

wkVar-erase-comm : (ρ : U.Wk m n) (x : Fin n) → wkVar (eraseWk ρ) x ≡ U.wkVar ρ x
wkVar-erase-comm id x = refl
wkVar-erase-comm (step ρ) x = cong _+1 (wkVar-erase-comm ρ x)
wkVar-erase-comm (lift ρ) x0 = refl
wkVar-erase-comm (lift ρ) (x +1) = cong _+1 (wkVar-erase-comm ρ x)

-- wk commutes with erase (modulo translating weakening to target language)
-- wk (eraseWk ρ) (erase t) ≡ erase (wk ρ t)

wk-erase-comm : (ρ : U.Wk m n) (t : U.Term n)
              → wk (eraseWk ρ) (erase t) ≡ erase (U.wk ρ t)
wk-erase-comm ρ (var x) = cong var (wkVar-erase-comm ρ x)
wk-erase-comm ρ U = refl
wk-erase-comm ρ (Π p , w ▷ F ▹ G) = refl
wk-erase-comm ρ (U.lam p t) =
  cong T.lam (wk-erase-comm (lift ρ) t)
wk-erase-comm ρ (t ∘⟨ 𝟘 ⟩ u) =
  cong (T._∘ ↯) (wk-erase-comm ρ t)
wk-erase-comm ρ (t ∘⟨ ω ⟩ u) =
  cong₂ T._∘_ (wk-erase-comm ρ t) (wk-erase-comm ρ u)
wk-erase-comm ρ (Σ q ▷ F ▹ G) = refl
wk-erase-comm ρ (prod! t u) =
  cong₂ T.prod (wk-erase-comm ρ t) (wk-erase-comm ρ u)
wk-erase-comm ρ (U.fst t) =
  cong T.fst (wk-erase-comm ρ t)
wk-erase-comm ρ (U.snd t) =
  cong T.snd (wk-erase-comm ρ t)
wk-erase-comm ρ (U.prodrec 𝟘 q A t u) =
  cong (Term.prodrec (Term.prod ↯ ↯)) (wk-erase-comm (lift (lift ρ)) u)
wk-erase-comm ρ (U.prodrec ω q A t u) =
  cong₂ T.prodrec (wk-erase-comm ρ t) (wk-erase-comm (lift (lift ρ)) u)
wk-erase-comm ρ ℕ = refl
wk-erase-comm ρ U.zero = refl
wk-erase-comm ρ (U.suc t) =
  cong T.suc (wk-erase-comm ρ t)
wk-erase-comm ρ (U.natrec p q r A z s n) =
  cong₃ T.natrec (wk-erase-comm ρ z)
                 (wk-erase-comm (lift (lift ρ)) s)
                 (wk-erase-comm ρ n)
wk-erase-comm ρ Unit = refl
wk-erase-comm ρ U.star = refl
wk-erase-comm ρ Empty = refl
wk-erase-comm ρ (Emptyrec p A t) = refl

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
... | t ∘⟨ 𝟘 ⟩ u =
  cong (T._∘ ↯) (wk-erase-comm (step id) t)
... | t ∘⟨ ω ⟩ u =
  cong₂ T._∘_ (wk-erase-comm (step id) t) (wk-erase-comm (step id) u)
... | Σ q ▷ F ▹ G = refl
... | prod! t u =
  cong₂ T.prod (wk-erase-comm (step id) t) (wk-erase-comm (step id) u)
... | U.fst t = cong T.fst (wk-erase-comm (step id) t)
... | U.snd t = cong T.snd (wk-erase-comm (step id) t)
... | U.prodrec 𝟘 q A t u =
  cong (Term.prodrec (Term.prod ↯ ↯)) (wk-erase-comm (lift (lift (step id))) u)
... | U.prodrec ω q A t u =
  cong₂ Term.prodrec (wk-erase-comm (step id) t)
                     (wk-erase-comm (lift (lift (step id))) u)
... | ℕ = refl
... | U.zero = refl
... | U.suc t = cong T.suc (wk-erase-comm (step id) t)
... | U.natrec p q r A z s n =
  cong₃ T.natrec (wk-erase-comm (step id) z)
                 (wk-erase-comm (lift (lift (step id))) s)
                 (wk-erase-comm (step id) n)
... | Unit = refl
... | U.star = refl
... | Empty = refl
... | Emptyrec p A t = refl

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
-- subst (eraseSubst σ) (erase t) ≡ erase (U.subst σ t)

subst-erase-comm : (σ : U.Subst m n) (t : U.Term n)
                 → T.subst (eraseSubst σ) (erase t) ≡ erase (U.subst σ t)
subst-erase-comm σ (var x) = refl
subst-erase-comm σ U = refl
subst-erase-comm σ (Π p , q ▷ F ▹ G) = refl
subst-erase-comm σ (U.lam p t) =
  cong Term.lam
    (begin
      T.subst (liftSubst (eraseSubst σ)) (erase t)
        ≡⟨ substVar-to-subst (liftSubsts-erase-comm 1) (erase t) ⟩
      T.subst (eraseSubst (U.liftSubst σ)) (erase t)
        ≡⟨ subst-erase-comm (U.liftSubst σ) t ⟩
      erase (U.subst (U.liftSubst σ) t) ∎)
  where open import Tools.Reasoning.PropositionalEquality
subst-erase-comm σ (t ∘⟨ 𝟘 ⟩ u) =
  cong (T._∘ ↯) (subst-erase-comm σ t)
subst-erase-comm σ (t ∘⟨ ω ⟩ u) =
  cong₂ T._∘_ (subst-erase-comm σ t) (subst-erase-comm σ u)
subst-erase-comm σ (Σ q ▷ F ▹ G) = refl
subst-erase-comm σ (prod! t u) =
  cong₂ T.prod (subst-erase-comm σ t) (subst-erase-comm σ u)
subst-erase-comm σ (U.fst t) = cong T.fst (subst-erase-comm σ t)
subst-erase-comm σ (U.snd t) = cong T.snd (subst-erase-comm σ t)
subst-erase-comm σ (U.prodrec 𝟘 q A t u) =
  cong (Term.prodrec (Term.prod ↯ ↯))
       (trans (substVar-to-subst (liftSubsts-erase-comm 2) (erase u))
              (subst-erase-comm (U.liftSubstn σ 2) u))
subst-erase-comm σ (U.prodrec ω q A t u) =
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
subst-erase-comm σ Unit = refl
subst-erase-comm σ U.star = refl
subst-erase-comm σ Empty = refl
subst-erase-comm σ (Emptyrec p A t) = refl

subst-undefined : (x : Fin (1+ n)) →
      erase (U.consSubst var Empty x) ≡
      T.consSubst var ↯ x
subst-undefined x0 = refl
subst-undefined (x +1) = refl

erase-consSubst-var : (σ : U.Subst m n) (a : U.Term m) (x : Fin (1+ n))
                    → T.consSubst (eraseSubst σ) (erase a) x
                    ≡ eraseSubst (U.consSubst σ a) x
erase-consSubst-var σ a x0 = refl
erase-consSubst-var σ a (x +1) = refl

erase-consSubst : (σ : U.Subst m n) (a : U.Term m) (t : T.Term (1+ n))
                → T.subst (T.consSubst (eraseSubst σ) (erase a)) t
                ≡ T.subst (eraseSubst (U.consSubst σ a)) t
erase-consSubst σ a t = substVar-to-subst (erase-consSubst-var σ a) t

-- Erased variables do not occur after extraction

erased-hasX : x ◂ 𝟘 ∈ γ → γ ▸ t → HasX x (erase t) → ⊥
erased-hasX erased γ▸t@var varₓ with unique-var-usage erased (valid-var-usage γ▸t)
... | ()
erased-hasX erased (lamₘ γ▸t) (lamₓ hasX) = erased-hasX (there erased) γ▸t hasX
erased-hasX erased (_∘ₘ_ {γ = γ} {δ = δ} {p = 𝟘} γ▸t δ▸u) (∘ₓˡ hasX)
  rewrite ≈ᶜ-eq (·ᶜ-zeroˡ δ)
  rewrite ≈ᶜ-eq (+ᶜ-identityʳ γ) =
  erased-hasX erased γ▸t hasX
erased-hasX erased (_∘ₘ_ {γ = γ} {δ = δ} {p = ω} γ▸t δ▸u) (∘ₓˡ hasX)
  rewrite ≈ᶜ-eq (·ᶜ-identityˡ δ) =
  erased-hasX erased (sub γ▸t (+ᶜ-decreasingˡ γ δ)) hasX
erased-hasX erased (_∘ₘ_ {γ = γ} {δ = δ} {p = ω} γ▸t δ▸u) (∘ₓʳ hasX)
  rewrite ≈ᶜ-eq (·ᶜ-identityˡ δ) =
  erased-hasX erased (sub δ▸u (+ᶜ-decreasingʳ γ δ)) hasX
erased-hasX erased (prodᵣₘ {γ = γ} {δ = δ} γ▸t δ▸u) (prodₓˡ hasX) =
  erased-hasX erased (sub γ▸t (+ᶜ-decreasingˡ γ δ)) hasX
erased-hasX erased (prodᵣₘ {γ = γ} {δ = δ} γ▸t δ▸u) (prodₓʳ hasX) =
  erased-hasX erased (sub δ▸u (+ᶜ-decreasingʳ γ δ)) hasX
erased-hasX erased (prodₚₘ γ▸t γ▸u) (prodₓˡ hasX) =
  erased-hasX erased γ▸t hasX
erased-hasX erased (prodₚₘ γ▸t γ▸u) (prodₓʳ hasX) =
  erased-hasX erased γ▸u hasX
erased-hasX erased (fstₘ γ▸t) (fstₓ hasX) =
  erased-hasX erased γ▸t hasX
erased-hasX erased (sndₘ γ▸t) (sndₓ hasX) =
  erased-hasX erased γ▸t hasX
erased-hasX erased (prodrecₘ {p = 𝟘} γ▸t δ▸u η▸A P) (prodrecₓˡ (prodₓˡ ()))
erased-hasX erased (prodrecₘ {p = 𝟘} γ▸t δ▸u η▸A P) (prodrecₓˡ (prodₓʳ ()))
erased-hasX erased (prodrecₘ {γ = γ} {δ = δ} {p = 𝟘} γ▸t δ▸u η▸A P) (prodrecₓʳ hasX)
  rewrite ≈ᶜ-eq (·ᶜ-zeroˡ γ)
  rewrite ≈ᶜ-eq (+ᶜ-identityˡ δ) =
  erased-hasX (there {q = 𝟘} (there {q = 𝟘} erased)) δ▸u hasX
erased-hasX erased (prodrecₘ {γ = γ} {δ = δ} {p = ω} γ▸t δ▸u η▸A P) (prodrecₓˡ hasX)
  rewrite ≈ᶜ-eq (·ᶜ-identityˡ γ) =
  erased-hasX erased (sub γ▸t (+ᶜ-decreasingˡ γ δ)) hasX
erased-hasX erased (prodrecₘ {γ = γ} {δ = δ} {p = ω} γ▸t δ▸u η▸A P) (prodrecₓʳ hasX)
  rewrite ≈ᶜ-eq (·ᶜ-identityˡ γ) =
  erased-hasX (there {q = ω} (there {q = ω} erased))
              (sub δ▸u (+ᶜ-decreasingʳ γ δ ∙ PE.refl ∙ PE.refl)) hasX
erased-hasX erased (sucₘ γ▸t) (sucₓ hasX) =
  erased-hasX erased γ▸t hasX
erased-hasX erased (natrecₘ {γ = γ} {δ = δ} {p = p} {r = r} {η = η} γ▸z δ▸s η▸n θ▸A)
            (natrecₓᶻ hasX) =
  erased-hasX erased (sub γ▸z (≤ᶜ-trans (⊛ᶜ-ineq₂ (γ ∧ᶜ η) (δ +ᶜ p ·ᶜ η) r)
                                        (∧ᶜ-decreasingˡ γ η)))
              hasX
erased-hasX erased (natrecₘ {γ = γ} {δ = δ} {p = p} {r = r} {η = η} γ▸z δ▸s η▸n θ▸A)
            (natrecₓˢ hasX) =
  erased-hasX (there {q = r} (there {q = p} erased))
              (sub δ▸s (γ′⊛δ′≤δ ∙ ≤-refl ∙ ≤-refl))
              hasX
  where
  open import Tools.Reasoning.PartialOrder ≤ᶜ-poset
  γ′⊛δ′≤δ = begin
    (γ ∧ᶜ η) ⊛ᶜ δ +ᶜ p ·ᶜ η ▷ r
      ≤⟨ ⊛ᶜ-ineq₁ (γ ∧ᶜ η) (δ +ᶜ p ·ᶜ η) r ⟩
    (δ +ᶜ p ·ᶜ η) +ᶜ r ·ᶜ ((γ ∧ᶜ η) ⊛ᶜ δ +ᶜ p ·ᶜ η ▷ r)
      ≤⟨ +ᶜ-decreasingˡ (δ +ᶜ p ·ᶜ η) _ ⟩
    δ +ᶜ p ·ᶜ η
      ≤⟨ +ᶜ-decreasingˡ δ (p ·ᶜ η) ⟩
    δ ∎
erased-hasX erased (natrecₘ {γ = γ} {δ = δ} {p = p} {r = r} {η = η} γ▸z δ▸s η▸n θ▸A) (natrecₓⁿ hasX) =
  erased-hasX erased (sub η▸n (≤ᶜ-trans (⊛ᶜ-ineq₂ (γ ∧ᶜ η) (δ +ᶜ p ·ᶜ η) r)
                                        (∧ᶜ-decreasingʳ γ η)))
              hasX
erased-hasX erased (sub δ▸t γ≤δ) hasX =
  erased-hasX (erased-var-sub erased γ≤δ) δ▸t hasX
