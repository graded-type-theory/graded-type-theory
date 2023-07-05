------------------------------------------------------------------------
-- Properties of the typing and reduction relations
------------------------------------------------------------------------

open import Definition.Typed.Restrictions

module Definition.Typed.Properties
  {ℓ} {M : Set ℓ}
  (R : Type-restrictions M)
  where

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed R

open import Tools.Empty using (⊥; ⊥-elim)
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n
    A A′ B B′ C U′ : Term n
    a b t u u′ v : Term n
    p p′ q : M

-- Escape context extraction

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

wf : Γ ⊢ A → ⊢ Γ
wf (ℕⱼ ⊢Γ) = ⊢Γ
wf (Emptyⱼ ⊢Γ) = ⊢Γ
wf (Unitⱼ ⊢Γ _) = ⊢Γ
wf (Uⱼ ⊢Γ) = ⊢Γ
wf (ΠΣⱼ F _ _) = wf F
wf (univ A) = wfTerm A

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
wfEqTerm (η-unit e e') = wfTerm e
wfEqTerm (prod-cong F _ _ _ _) = wf F
wfEqTerm (fst-cong _ _ a) = wfEqTerm a
wfEqTerm (snd-cong _ _ a) = wfEqTerm a
wfEqTerm (prodrec-cong F _ _ _ _ _) = wf F
wfEqTerm (prodrec-β F _ _ _ _ _ _ _) = wf F
wfEqTerm (Σ-η _ _ x _ _ _) = wfTerm x
wfEqTerm (Σ-β₁ _ _ x _ _ _) = wfTerm x
wfEqTerm (Σ-β₂ _ _ x _ _ _) = wfTerm x

wfEq : Γ ⊢ A ≡ B → ⊢ Γ
wfEq (univ A≡B) = wfEqTerm A≡B
wfEq (refl A) = wf A
wfEq (sym A≡B) = wfEq A≡B
wfEq (trans A≡B B≡C) = wfEq A≡B
wfEq (ΠΣ-cong F _ _ _) = wf F


-- Reduction is a subset of conversion

subsetTerm : Γ ⊢ t ⇒ u ∷ A → Γ ⊢ t ≡ u ∷ A
subsetTerm (natrec-subst F z s n⇒n′) =
  natrec-cong F (refl F) (refl z) (refl s) (subsetTerm n⇒n′)
subsetTerm (natrec-zero F z s) = natrec-zero F z s
subsetTerm (natrec-suc F z s n) = natrec-suc F z s n
subsetTerm (emptyrec-subst A n⇒n′) =
  emptyrec-cong (refl A) (subsetTerm n⇒n′)
subsetTerm (app-subst t⇒u a) =
  app-cong (subsetTerm t⇒u) (refl a)
subsetTerm (β-red A B t a p≡p′ ok) = β-red A B t a p≡p′ ok
subsetTerm (conv t⇒u A≡B) = conv (subsetTerm t⇒u) A≡B
subsetTerm (fst-subst F G x) = fst-cong F G (subsetTerm x)
subsetTerm (snd-subst F G x) = snd-cong F G (subsetTerm x)
subsetTerm (prodrec-subst F G A u t⇒t′ ok) =
  prodrec-cong F G (refl A) (subsetTerm t⇒t′) (refl u) ok
subsetTerm (prodrec-β F G A t t′ u eq ok) =
  prodrec-β F G A t t′ u eq ok
subsetTerm (Σ-β₁ F G x x₁ x₂ ok) = Σ-β₁ F G x x₁ x₂ ok
subsetTerm (Σ-β₂ F G x x₁ x₂ ok) = Σ-β₂ F G x x₁ x₂ ok

subset : Γ ⊢ A ⇒ B → Γ ⊢ A ≡ B
subset (univ A⇒B) = univ (subsetTerm A⇒B)

subset*Term : Γ ⊢ t ⇒* u ∷ A → Γ ⊢ t ≡ u ∷ A
subset*Term (id t) = refl t
subset*Term (t⇒t′ ⇨ t⇒*u) = trans (subsetTerm t⇒t′) (subset*Term t⇒*u)

subset* : Γ ⊢ A ⇒* B → Γ ⊢ A ≡ B
subset* (id A) = refl A
subset* (A⇒A′ ⇨ A′⇒*B) = trans (subset A⇒A′) (subset* A′⇒*B)


-- Can extract left-part of a reduction

redFirstTerm :{Γ : Con Term n} → Γ ⊢ t ⇒ u ∷ A → Γ ⊢ t ∷ A
redFirstTerm (conv t⇒u A≡B) = conv (redFirstTerm t⇒u) A≡B
redFirstTerm (app-subst t⇒u a) = (redFirstTerm t⇒u) ∘ⱼ a
redFirstTerm (β-red A B t a PE.refl ok) =
  conv (lamⱼ A t ok) (ΠΣ-cong A (refl A) (refl B) ok) ∘ⱼ a
redFirstTerm (natrec-subst F z s n⇒n′) = natrecⱼ F z s (redFirstTerm n⇒n′)
redFirstTerm (natrec-zero F z s) = natrecⱼ F z s (zeroⱼ (wfTerm z))
redFirstTerm (natrec-suc F z s n) = natrecⱼ F z s (sucⱼ n)
redFirstTerm (emptyrec-subst A n⇒n′) = emptyrecⱼ A (redFirstTerm n⇒n′)
redFirstTerm (fst-subst F G x) = fstⱼ F G (redFirstTerm x)
redFirstTerm (snd-subst F G x) = sndⱼ F G (redFirstTerm x)
redFirstTerm (prodrec-subst F G A u t⇒t′ ok) =
  prodrecⱼ F G A (redFirstTerm t⇒t′) u ok
redFirstTerm (prodrec-β F G A t t′ u PE.refl ok) =
  prodrecⱼ F G A
    (conv (prodⱼ F G t t′ ok) (ΠΣ-cong F (refl F) (refl G) ok))
    u ok
redFirstTerm (Σ-β₁ F G x x₁ PE.refl ok) =
  fstⱼ F G
    (conv (prodⱼ F G x x₁ ok) (ΠΣ-cong F (refl F) (refl G) ok))
redFirstTerm (Σ-β₂ F G x x₁ PE.refl ok) =
  sndⱼ F G
    (conv (prodⱼ F G x x₁ ok) (ΠΣ-cong F (refl F) (refl G) ok))

redFirst :{Γ : Con Term n} → Γ ⊢ A ⇒ B → Γ ⊢ A
redFirst (univ A⇒B) = univ (redFirstTerm A⇒B)

redFirst*Term : {Γ : Con Term n} → Γ ⊢ t ⇒* u ∷ A → Γ ⊢ t ∷ A
redFirst*Term (id t) = t
redFirst*Term (t⇒t′ ⇨ t′⇒*u) = redFirstTerm t⇒t′

redFirst* : {Γ : Con Term n} → Γ ⊢ A ⇒* B → Γ ⊢ A
redFirst* (id A) = A
redFirst* (A⇒A′ ⇨ A′⇒*B) = redFirst A⇒A′

-- No neutral terms are well-formed in an empty context

noNe : ε ⊢ t ∷ A → Neutral t → ⊥
noNe (conv ⊢t x) n = noNe ⊢t n
noNe (var x₁ ()) (var x)
noNe (⊢t ∘ⱼ ⊢t₁) (∘ₙ neT) = noNe ⊢t neT
noNe (fstⱼ _ _ ⊢t) (fstₙ neT) = noNe ⊢t neT
noNe (sndⱼ _ _ ⊢t) (sndₙ neT) = noNe ⊢t neT
noNe (natrecⱼ x ⊢t ⊢t₁ ⊢t₂) (natrecₙ neT) = noNe ⊢t₂ neT
noNe (prodrecⱼ _ _ _ ⊢t _ _) (prodrecₙ neT) = noNe ⊢t neT
noNe (emptyrecⱼ A ⊢e) (emptyrecₙ neT) = noNe ⊢e neT

-- Neutrals do not weak head reduce

neRedTerm : (d : Γ ⊢ t ⇒ u ∷ A) (n : Neutral t) → ⊥
neRedTerm (conv d x) n = neRedTerm d n
neRedTerm (app-subst d x) (∘ₙ n) = neRedTerm d n
neRedTerm (β-red _ _ _ _ _ _) (∘ₙ ())
neRedTerm (natrec-subst x x₁ x₂ d) (natrecₙ n₁) = neRedTerm d n₁
neRedTerm (natrec-zero x x₁ x₂) (natrecₙ ())
neRedTerm (natrec-suc x x₁ x₂ x₃) (natrecₙ ())
neRedTerm (emptyrec-subst x d) (emptyrecₙ n₁) = neRedTerm d n₁
neRedTerm (fst-subst _ _ d) (fstₙ n) = neRedTerm d n
neRedTerm (snd-subst _ _ d) (sndₙ n) = neRedTerm d n
neRedTerm (prodrec-subst _ _ _ _ d _) (prodrecₙ n) = neRedTerm d n
neRedTerm (prodrec-β _ _ _ _ _ _ _ _) (prodrecₙ ())
neRedTerm (Σ-β₁ _ _ _ _ _ _) (fstₙ ())
neRedTerm (Σ-β₂ _ _ _ _ _ _) (sndₙ ())

neRed : (d : Γ ⊢ A ⇒ B) (N : Neutral A) → ⊥
neRed (univ x) N = neRedTerm x N

-- Whnfs do not weak head reduce

whnfRedTerm : (d : Γ ⊢ t ⇒ u ∷ A) (w : Whnf t) → ⊥
whnfRedTerm (conv d x) w = whnfRedTerm d w
whnfRedTerm (app-subst d x) (ne (∘ₙ x₁)) = neRedTerm d x₁
whnfRedTerm (β-red _ _ _ _ _ _) (ne (∘ₙ ()))
whnfRedTerm (natrec-subst x x₁ x₂ d) (ne (natrecₙ x₃)) = neRedTerm d x₃
whnfRedTerm (natrec-zero x x₁ x₂) (ne (natrecₙ ()))
whnfRedTerm (natrec-suc x x₁ x₂ x₃) (ne (natrecₙ ()))
whnfRedTerm (emptyrec-subst x d) (ne (emptyrecₙ x₂)) = neRedTerm d x₂
whnfRedTerm (fst-subst _ _ d) (ne (fstₙ n)) = neRedTerm d n
whnfRedTerm (snd-subst _ _ d) (ne (sndₙ n)) = neRedTerm d n
whnfRedTerm (prodrec-subst _ _ _ _ d _) (ne (prodrecₙ n)) =
  neRedTerm d n
whnfRedTerm (prodrec-β _ _ _ _ _ _ _ _) (ne (prodrecₙ ()))
whnfRedTerm (Σ-β₁ _ _ _ _ _ _) (ne (fstₙ ()))
whnfRedTerm (Σ-β₂ _ _ _ _ _ _) (ne (sndₙ ()))

whnfRed : (d : Γ ⊢ A ⇒ B) (w : Whnf A) → ⊥
whnfRed (univ x) w = whnfRedTerm x w

whnfRed*Term : (d : Γ ⊢ t ⇒* u ∷ A) (w : Whnf t) → t PE.≡ u
whnfRed*Term (id x) _ = PE.refl
whnfRed*Term (conv x x₁ ⇨ d) w = ⊥-elim (whnfRedTerm x w)
whnfRed*Term (x ⇨ d) (ne x₁) = ⊥-elim (neRedTerm x x₁)

whnfRed* : (d : Γ ⊢ A ⇒* B) (w : Whnf A) → A PE.≡ B
whnfRed* (id x) w = PE.refl
whnfRed* (x ⇨ d) w = ⊥-elim (whnfRed x w)

-- Whr is deterministic

whrDetTerm : (d : Γ ⊢ t ⇒ u ∷ A) (d′ : Γ ⊢ t ⇒ u′ ∷ A′) → u PE.≡ u′
whrDetTerm (conv d x) d′ = whrDetTerm d d′
whrDetTerm d (conv d′ x₁) = whrDetTerm d d′
whrDetTerm (app-subst d x) (app-subst d′ x₁) rewrite whrDetTerm d d′ = PE.refl
whrDetTerm (β-red _ _ _ _ _ _) (β-red _ _ _ _ _ _) = PE.refl
whrDetTerm (fst-subst _ _ x) (fst-subst _ _ y) rewrite whrDetTerm x y = PE.refl
whrDetTerm (snd-subst _ _ x) (snd-subst _ _ y) rewrite whrDetTerm x y = PE.refl
whrDetTerm (Σ-β₁ _ _ _ _ _ _) (Σ-β₁ _ _ _ _ _ _) = PE.refl
whrDetTerm (Σ-β₂ _ _ _ _ _ _) (Σ-β₂ _ _ _ _ _ _) = PE.refl
whrDetTerm (natrec-subst x x₁ x₂ d) (natrec-subst x₃ x₄ x₅ d′) rewrite whrDetTerm d d′ = PE.refl
whrDetTerm (natrec-zero x x₁ x₂) (natrec-zero x₃ x₄ x₅) = PE.refl
whrDetTerm (natrec-suc x x₁ x₂ x₃) (natrec-suc x₄ x₅ x₆ x₇) = PE.refl
whrDetTerm (prodrec-subst _ _ _ _ d _) (prodrec-subst _ _ _ _ d′ _)
  rewrite whrDetTerm d d′ = PE.refl
whrDetTerm (prodrec-β _ _ _ _ _ _ _ _) (prodrec-β _ _ _ _ _ _ _ _) =
  PE.refl
whrDetTerm (emptyrec-subst x d) (emptyrec-subst x₂ d′) rewrite whrDetTerm d d′ = PE.refl

whrDetTerm (app-subst d _) (β-red _ _ _ _ _ _) =
  ⊥-elim (whnfRedTerm d lamₙ)
whrDetTerm (β-red _ _ _ _ _ _) (app-subst d _) =
  ⊥-elim (whnfRedTerm d lamₙ)
whrDetTerm (natrec-subst x x₁ x₂ d) (natrec-zero x₃ x₄ x₅) = ⊥-elim (whnfRedTerm d zeroₙ)
whrDetTerm (natrec-subst x x₁ x₂ d) (natrec-suc x₃ x₄ x₅ x₆) = ⊥-elim (whnfRedTerm d sucₙ)
whrDetTerm (natrec-zero x x₁ x₂) (natrec-subst x₃ x₄ x₅ d′) = ⊥-elim (whnfRedTerm d′ zeroₙ)
whrDetTerm (natrec-suc x x₁ x₂ x₃) (natrec-subst x₄ x₅ x₆ d′) = ⊥-elim (whnfRedTerm d′ sucₙ)
whrDetTerm (fst-subst _ _ x) (Σ-β₁ _ _ _ _ _ _) =
  ⊥-elim (whnfRedTerm x prodₙ)
whrDetTerm (snd-subst _ _ x) (Σ-β₂ _ _ _ _ _ _) =
  ⊥-elim (whnfRedTerm x prodₙ)
whrDetTerm (Σ-β₁ _ _ _ _ _ _) (fst-subst _ _ y) =
  ⊥-elim (whnfRedTerm y prodₙ)
whrDetTerm (Σ-β₂ _ _ _ _ _ _) (snd-subst _ _ y) =
  ⊥-elim (whnfRedTerm y prodₙ)
whrDetTerm
  (prodrec-subst _ _ _ _ t⇒ _) (prodrec-β _ _ _ _ _ _ _ _) =
  ⊥-elim (whnfRedTerm t⇒ prodₙ)
whrDetTerm
  (prodrec-β _ _ _ _ _ _ _ _) (prodrec-subst _ _ _ _ t⇒ _) =
  ⊥-elim (whnfRedTerm t⇒ prodₙ)

whrDet : (d : Γ ⊢ A ⇒ B) (d′ : Γ ⊢ A ⇒ B′) → B PE.≡ B′
whrDet (univ x) (univ x₁) = whrDetTerm x x₁

whrDet↘Term : (d : Γ ⊢ t ↘ u ∷ A) (d′ : Γ ⊢ t ⇒* u′ ∷ A) → Γ ⊢ u′ ⇒* u ∷ A
whrDet↘Term (proj₁ , proj₂) (id x) = proj₁
whrDet↘Term (id x , proj₂) (x₁ ⇨ d′) = ⊥-elim (whnfRedTerm x₁ proj₂)
whrDet↘Term (x ⇨ proj₁ , proj₂) (x₁ ⇨ d′) =
  whrDet↘Term (PE.subst (λ x₂ → _ ⊢ x₂ ↘ _ ∷ _) (whrDetTerm x x₁) (proj₁ , proj₂)) d′

whrDet*Term : (d : Γ ⊢ t ↘ u ∷ A) (d′ : Γ ⊢ t ↘ u′ ∷ A′) → u PE.≡ u′
whrDet*Term (id x , proj₂) (id x₁ , proj₄) = PE.refl
whrDet*Term (id x , proj₂) (x₁ ⇨ proj₃ , proj₄) = ⊥-elim (whnfRedTerm x₁ proj₂)
whrDet*Term (x ⇨ proj₁ , proj₂) (id x₁ , proj₄) = ⊥-elim (whnfRedTerm x proj₄)
whrDet*Term (x ⇨ proj₁ , proj₂) (x₁ ⇨ proj₃ , proj₄) =
  whrDet*Term (proj₁ , proj₂) (PE.subst (λ x₂ → _ ⊢ x₂ ↘ _ ∷ _)
                                    (whrDetTerm x₁ x) (proj₃ , proj₄))

whrDet* : (d : Γ ⊢ A ↘ B) (d′ : Γ ⊢ A ↘ B′) → B PE.≡ B′
whrDet* (id x , proj₂) (id x₁ , proj₄) = PE.refl
whrDet* (id x , proj₂) (x₁ ⇨ proj₃ , proj₄) = ⊥-elim (whnfRed x₁ proj₂)
whrDet* (x ⇨ proj₁ , proj₂) (id x₁ , proj₄) = ⊥-elim (whnfRed x proj₄)
whrDet* (A⇒A′ ⇨ A′⇒*B , whnfB) (A⇒A″ ⇨ A″⇒*B′ , whnfB′) =
  whrDet* (A′⇒*B , whnfB) (PE.subst (λ x → _ ⊢ x ↘ _)
                                     (whrDet A⇒A″ A⇒A′)
                                     (A″⇒*B′ , whnfB′))

-- Reduction does not include η-expansion for the unit type with
-- η-equality (for WHNFs): if a WHNF t reduces to star (at type Unit),
-- then t is equal to star.

no-η-expansion-Unit : Whnf t → Γ ⊢ t ⇒* star ∷ Unit → t PE.≡ star
no-η-expansion-Unit = flip whnfRed*Term

-- Reduction does not include η-expansion for Σ-types with η-equality
-- (for WHNFs): if a WHNF t reduces to prodₚ p u v (at type
-- Σₚ p′ , q ▷ A ▹ B), then t is equal to prodₚ p u v.

no-η-expansion-Σₚ :
  Whnf t →
  Γ ⊢ t ⇒* prodₚ p u v ∷ Σₚ p′ , q ▷ A ▹ B →
  t PE.≡ prodₚ p u v
no-η-expansion-Σₚ = flip whnfRed*Term

-- Identity of syntactic reduction

idRed:*: : Γ ⊢ A → Γ ⊢ A :⇒*: A
idRed:*: A = [ A , A , id A ]

idRedTerm:*: : Γ ⊢ t ∷ A → Γ ⊢ t :⇒*: t ∷ A
idRedTerm:*: t = [ t , t , id t ]

-- U cannot be a term

UnotInA : Γ ⊢ U ∷ A → ⊥
UnotInA (conv U∷U x) = UnotInA U∷U

UnotInA[t] : t [ a ]₀ PE.≡ U
         → Γ ⊢ a ∷ A
         → Γ ∙ A ⊢ t ∷ B
         → ⊥
UnotInA[t] () x₁ (ℕⱼ x₂)
UnotInA[t] () x₁ (Emptyⱼ x₂)
UnotInA[t] () _  (ΠΣⱼ _ _ _)
UnotInA[t] x₁ x₂ (var x₃ here) rewrite x₁ = UnotInA x₂
UnotInA[t] () x₂ (var x₃ (there x₄))
UnotInA[t] () _  (lamⱼ _ _ _)
UnotInA[t] () x₁ (x₂ ∘ⱼ x₃)
UnotInA[t] () x₁ (zeroⱼ x₂)
UnotInA[t] () x₁ (sucⱼ x₂)
UnotInA[t] () x₁ (natrecⱼ x₂ x₃ x₄ x₅)
UnotInA[t] () x₁ (emptyrecⱼ x₂ x₃)
UnotInA[t] x x₁ (conv x₂ x₃) = UnotInA[t] x x₁ x₂

UnotInA[t,u] : t [ consSubst (consSubst idSubst u) u′ ] PE.≡ U
              → Γ ⊢ u ∷ A
              → Γ ⊢ u′ ∷ B [ a ]₀
              → Γ ∙ A ∙ B ⊢ t ∷ C
              → ⊥
UnotInA[t,u] PE.refl u u′ (var x here) = UnotInA u′
UnotInA[t,u] PE.refl u u′ (var x (there here)) = UnotInA u
UnotInA[t,u] eq u u′ (conv t x) = UnotInA[t,u] eq u u′ t

redU*Term′ : U′ PE.≡ U → Γ ⊢ A ⇒ U′ ∷ B → ⊥
redU*Term′ U′≡U (conv A⇒U x) = redU*Term′ U′≡U A⇒U
redU*Term′ () (app-subst A⇒U x)
redU*Term′ U′≡U (β-red _ _ ⊢t ⊢u _ _) = UnotInA[t] U′≡U ⊢u ⊢t
redU*Term′ () (natrec-subst x x₁ x₂ A⇒U)
redU*Term′ PE.refl (natrec-zero x x₁ x₂) = UnotInA x₁
redU*Term′ U′≡U (natrec-suc x x₁ x₂ x₃) =
  UnotInA[t,u] U′≡U x₃ (natrecⱼ x x₁ x₂ x₃) x₂
redU*Term′ U′≡U (prodrec-β _ _ _ ⊢t ⊢u ⊢v _ _) =
  UnotInA[t,u] U′≡U ⊢t ⊢u ⊢v
redU*Term′ () (emptyrec-subst x A⇒U)
redU*Term′ PE.refl (Σ-β₁ _ _ x _ _ _) = UnotInA x
redU*Term′ PE.refl (Σ-β₂ _ _ _ x _ _) = UnotInA x

redU*Term : Γ ⊢ A ⇒* U ∷ B → ⊥
redU*Term (id x) = UnotInA x
redU*Term (x ⇨ A⇒*U) = redU*Term A⇒*U

-- Nothing reduces to U

redU : Γ ⊢ A ⇒ U → ⊥
redU (univ x) = redU*Term′ PE.refl x

redU* : Γ ⊢ A ⇒* U → A PE.≡ U
redU* (id x) = PE.refl
redU* (x ⇨ A⇒*U) rewrite redU* A⇒*U = ⊥-elim (redU x)

det∈ : ∀ {x} → x ∷ A ∈ Γ → x ∷ B ∈ Γ → A PE.≡ B
det∈ here here = PE.refl
det∈ (there x) (there y) = PE.cong wk1 (det∈ x y)
