------------------------------------------------------------------------
-- The typing relation is an instance of the abstract set of
-- equality relations.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions

module Definition.Typed.EqRelInstance
  {a} {M : Set a}
  (R : Type-restrictions M)
  where

open import Definition.Typed R
open import Definition.Typed.Weakening R
open import Definition.Typed.Reduction R
open import Definition.Typed.EqualityRelation R

open import Tools.Function


-- Judgmental instance of the equality relation

instance eqRelInstance : EqRelSet
eqRelInstance = record {
  _⊢_≅_ = _⊢_≡_;
  _⊢_≅_∷_ = _⊢_≡_∷_;
  _⊢_~_∷_ = _⊢_≡_∷_;
  ~-to-≅ₜ = idᶠ;
  ≅-eq = idᶠ;
  ≅ₜ-eq = idᶠ;
  ≅-univ = univ;
  ≅-sym = sym;
  ≅ₜ-sym = sym;
  ~-sym = sym;
  ≅-trans = trans;
  ≅ₜ-trans = trans;
  ~-trans = trans;
  ≅-conv = conv;
  ~-conv = conv;
  ≅-wk = wkEq;
  ≅ₜ-wk = wkEqTerm;
  ~-wk = wkEqTerm;
  ≅-red = reduction;
  ≅ₜ-red = reductionₜ;
  ≅-Urefl = refl ∘ᶠ Uⱼ;
  ≅-ℕrefl = refl ∘ᶠ ℕⱼ;
  ≅ₜ-ℕrefl = refl ∘ᶠ ℕⱼ;
  ≅-Emptyrefl = refl ∘ᶠ Emptyⱼ;
  ≅ₜ-Emptyrefl = refl ∘ᶠ Emptyⱼ;
  ≅-Unitrefl = λ ⊢Γ → refl ∘ᶠ Unitⱼ ⊢Γ;
  ≅ₜ-Unitrefl = λ ⊢Γ → refl ∘ᶠ Unitⱼ ⊢Γ;
  ≅ₜ-η-unit = η-unit;
  ≅-ΠΣ-cong = ΠΣ-cong;
  ≅ₜ-ΠΣ-cong = ΠΣ-cong;
  ≅ₜ-zerorefl = refl ∘ᶠ zeroⱼ;
  ≅-suc-cong = suc-cong;
  ≅-prod-cong = prod-cong;
  ≅-η-eq = λ x x₁ x₂ x₃ x₄ x₅ → η-eq x x₁ x₂ x₅;
  ≅-Σ-η = λ ⊢F ⊢G ⊢p ⊢r _ _ fst≡ snd≡ → Σ-η ⊢F ⊢G ⊢p ⊢r fst≡ snd≡;
  ~-var = refl;
  ~-app = app-cong;
  ~-fst = fst-cong;
  ~-snd = snd-cong;
  ~-natrec = natrec-cong;
  ~-prodrec = prodrec-cong;
  ~-Emptyrec = Emptyrec-cong }
