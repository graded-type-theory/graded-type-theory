{-# OPTIONS --without-K --safe #-}

open import Tools.Relation

module Definition.Typed.EqRelInstance {a ℓ} (M′ : Setoid a ℓ) where

open Setoid M′ using () renaming (Carrier to M)

open import Definition.Untyped M
open import Definition.Typed M′
open import Definition.Typed.Weakening M′
open import Definition.Typed.Reduction M′
open import Definition.Typed.EqualityRelation M′

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
  ≅-Unitrefl = refl ∘ᶠ Unitⱼ;
  ≅ₜ-Unitrefl = refl ∘ᶠ Unitⱼ;
  ≅ₜ-η-unit = η-unit;
  ≅-Π-cong = Π-cong;
  ≅ₜ-Π-cong = Π-cong;
  ≅-Σ-cong = Σ-cong;
  ≅ₜ-Σ-cong = Σ-cong;
  ≅ₜ-zerorefl = refl ∘ᶠ zeroⱼ;
  ≅-suc-cong = suc-cong;
  ≅-η-eq = λ x x₁ x₂ x₃ x₄ x₅ → η-eq x x₁ x₂ x₅;
  ≅-Σ-η = λ ⊢F ⊢G ⊢p ⊢r pProd rProd fst≡ snd≡ → Σ-η ⊢F ⊢G ⊢p ⊢r fst≡ snd≡;
  ~-var = refl;
  ~-app = app-cong;
  ~-fst = fst-cong;
  ~-snd = snd-cong;
  ~-natrec = natrec-cong;
  ~-Emptyrec = Emptyrec-cong }
