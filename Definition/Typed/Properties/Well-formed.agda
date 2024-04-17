------------------------------------------------------------------------
-- Some lemmas that are re-exported from Definition.Typed.Properties
------------------------------------------------------------------------

-- This module is imported from Graded.Derived.Erased.Typed.Primitive,
-- which is imported from Definition.Typed.Properties.

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Properties.Well-formed
  {ℓ} {M : Set ℓ}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.Untyped M
open import Definition.Typed R

open import Tools.Nat

private variable
  Γ       : Con Term _
  A B t u : Term _

-- If a term is well-typed with respect to Γ, then Γ is well-formed.

wfTerm : Γ ⊢ t ∷ A → ⊢ Γ
wfTerm (ℕⱼ ⊢Γ) = ⊢Γ
wfTerm (Emptyⱼ ⊢Γ) = ⊢Γ
wfTerm (Unitⱼ ⊢Γ _) = ⊢Γ
wfTerm (ΠΣⱼ F _ _) = wfTerm F
wfTerm (var ⊢Γ x₁) = ⊢Γ
wfTerm (lamⱼ _ t _) with wfTerm t
wfTerm (lamⱼ _ t _) | ⊢Γ ∙ _ = ⊢Γ
wfTerm (g ∘ⱼ a) = wfTerm a
wfTerm (zeroⱼ ⊢Γ) = ⊢Γ
wfTerm (sucⱼ n) = wfTerm n
wfTerm (natrecⱼ F z s n) = wfTerm z
wfTerm (prodrecⱼ _ _ _ t _ _) = wfTerm t
wfTerm (emptyrecⱼ A e) = wfTerm e
wfTerm (starⱼ ⊢Γ _) = ⊢Γ
wfTerm (conv t A≡B) = wfTerm t
wfTerm (prodⱼ _ _ a _ _) = wfTerm a
wfTerm (fstⱼ _ _ a) = wfTerm a
wfTerm (sndⱼ _ _ a) = wfTerm a
wfTerm (Idⱼ _ ⊢t _) = wfTerm ⊢t
wfTerm (rflⱼ ⊢t) = wfTerm ⊢t
wfTerm (Jⱼ _ ⊢t _ _ _ _) = wfTerm ⊢t
wfTerm (Kⱼ ⊢t _ _ _ _) = wfTerm ⊢t
wfTerm ([]-congⱼ ⊢t _ _ _) = wfTerm ⊢t
wfTerm (unitrecⱼ _ ⊢t _ _) = wfTerm ⊢t

-- If a type is well-typed with respect to Γ, then Γ is well-formed.

wf : Γ ⊢ A → ⊢ Γ
wf (ℕⱼ ⊢Γ) = ⊢Γ
wf (Emptyⱼ ⊢Γ) = ⊢Γ
wf (Unitⱼ ⊢Γ _) = ⊢Γ
wf (Uⱼ ⊢Γ) = ⊢Γ
wf (ΠΣⱼ F _ _) = wf F
wf (Idⱼ ⊢t _) = wfTerm ⊢t
wf (univ A) = wfTerm A

-- If a term equality is well-formed with respect to Γ, then Γ is
-- well-formed.

wfEqTerm : Γ ⊢ t ≡ u ∷ A → ⊢ Γ
wfEqTerm (refl t) = wfTerm t
wfEqTerm (sym t≡u) = wfEqTerm t≡u
wfEqTerm (trans t≡u u≡r) = wfEqTerm t≡u
wfEqTerm (conv t≡u A≡B) = wfEqTerm t≡u
wfEqTerm (ΠΣ-cong _ F≡H _ _) = wfEqTerm F≡H
wfEqTerm (app-cong f≡g a≡b) = wfEqTerm f≡g
wfEqTerm (β-red _ _ _ a _ _) = wfTerm a
wfEqTerm (η-eq F f g f0≡g0) = wfTerm f
wfEqTerm (suc-cong n) = wfEqTerm n
wfEqTerm (natrec-cong _ F≡F′ z≡z′ s≡s′ n≡n′) = wfEqTerm z≡z′
wfEqTerm (natrec-zero F z s) = wfTerm z
wfEqTerm (natrec-suc _ _ _ n) = wfTerm n
wfEqTerm (emptyrec-cong A≡A' e≡e') = wfEqTerm e≡e'
wfEqTerm (η-unit e _ _) = wfTerm e
wfEqTerm (prod-cong F _ _ _ _) = wf F
wfEqTerm (fst-cong _ _ a) = wfEqTerm a
wfEqTerm (snd-cong _ _ a) = wfEqTerm a
wfEqTerm (prodrec-cong F _ _ _ _ _) = wf F
wfEqTerm (prodrec-β F _ _ _ _ _ _ _) = wf F
wfEqTerm (Σ-η _ _ x _ _ _) = wfTerm x
wfEqTerm (Σ-β₁ _ _ x _ _ _) = wfTerm x
wfEqTerm (Σ-β₂ _ _ x _ _ _) = wfTerm x
wfEqTerm (Id-cong _ t₁≡t₂ _) = wfEqTerm t₁≡t₂
wfEqTerm (J-cong _ _ _ t₁≡t₂ _ _ _ _) = wfEqTerm t₁≡t₂
wfEqTerm (J-β _ ⊢t _ _ _) = wfTerm ⊢t
wfEqTerm (K-cong _ _ t₁≡t₂ _ _ _ _) = wfEqTerm t₁≡t₂
wfEqTerm (K-β ⊢t _ _ _) = wfTerm ⊢t
wfEqTerm ([]-cong-cong _ t₁≡t₂ _ _ _) = wfEqTerm t₁≡t₂
wfEqTerm ([]-cong-β ⊢t _ _) = wfTerm ⊢t
wfEqTerm (unitrec-cong _ t≡t′ _ _ _) = wfEqTerm t≡t′
wfEqTerm (unitrec-β _ ⊢u _ _) = wfTerm ⊢u
wfEqTerm (unitrec-β-η _ ⊢u _ _ _) = wfTerm ⊢u

-- If a type equality is well-formed with respect to Γ, then Γ is
-- well-formed.

wfEq : Γ ⊢ A ≡ B → ⊢ Γ
wfEq (univ A≡B) = wfEqTerm A≡B
wfEq (refl A) = wf A
wfEq (sym A≡B) = wfEq A≡B
wfEq (trans A≡B B≡C) = wfEq A≡B
wfEq (ΠΣ-cong F _ _ _) = wf F
wfEq (Id-cong A₁≡A₂ _ _) = wfEq A₁≡A₂

opaque

  -- If Γ ⊢ A holds, then ⊢ Γ ∙ A also holds.

  ⊢→⊢∙ : Γ ⊢ A → ⊢ Γ ∙ A
  ⊢→⊢∙ ⊢A = wf ⊢A ∙ ⊢A

opaque

  -- A lemma which could perhaps be used to make certain proofs more
  -- readable.

  infixl 24 _∙[_]

  _∙[_] : ⊢ Γ → (⊢ Γ → Γ ⊢ A) → ⊢ Γ ∙ A
  ⊢Γ ∙[ f ] = ⊢→⊢∙ (f ⊢Γ)

-- An example of how _∙[_] can be used.

_ : ⊢ ε ∙ ℕ ∙ U ∙ Empty
_ = ε ∙[ ℕⱼ ] ∙[ Uⱼ ] ∙[ Emptyⱼ ]
